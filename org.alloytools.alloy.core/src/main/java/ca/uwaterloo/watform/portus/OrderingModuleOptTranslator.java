package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.DomainElement;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * The ordering module optimization, where we hardcode a "next" function and a "first" element
 * for symmetry breaking.
 */
final class OrderingModuleOptTranslator extends AbstractTranslator {

    private static final class OrderInfo {
        private final Sig ordSig;
        private final Sig sig;
        private final Sig.Field first;
        private final Sig.Field next;
        private final String nextFuncName;

        public OrderInfo(Sig ordSig, Sig sig, Sig.Field first, Sig.Field next, TranslationContext context) {
            this.ordSig = ordSig;
            this.sig = sig;
            this.first = first;
            this.next = next;
            this.nextFuncName = generateNextFuncName();
            validate(context);
        }

        private String generateNextFuncName() {
            // Ensure two orderings on the same sig get the same func name
            return "next_" + sig.label;
        }

        private void validate(TranslationContext context) {
            // We require an exact scope so we can allocate the domain elements
            if (!context.scoper.isExact(sig)) {
                throw new ErrorFatal("Ordered signatures must have an exact scope.");
            }
            if (sig.builtin) {
                throw new ErrorFatal("Portus doesn't support ordering builtin signatures: " + sig.label);
            }
            if (context.sortPolicy.getSort(sig) == null) {
                throw new ErrorFatal("Sig " + sig.label + " can't be ordered because Portus can't determine a sort");
            }
            if (context.sortPolicy.getDomainElementRange(sig, context.scoper) == null) {
                // this probably shouldn't happen
                throw new ErrorFatal("Sig " + sig.label + " can't be ordered for unknown reasons");
            }

            if (!first.decl().expr.deNOP().isSame(sig.setOf())) {
                throw new ErrorFatal("The First field in pred/totalOrder must be have the type of the ordered sig");
            }
            if (!next.decl().expr.deNOP().isSame(sig.product(sig))) {
                throw new ErrorFatal(
                        "The Next field in pred/totalOrder must have type S->S, where S is the ordered sig");
            }
        }

        public boolean matchesFirstField(Sig.Field candidateFirst) {
            return first.isSame(candidateFirst);
        }

        public boolean matchesNextField(Sig.Field candidateNext) {
            return next.isSame(candidateNext);
        }

        public boolean matchesFirstUsage(Expr candidateFirst) {
            Sig.Field firstField = extractDottedField(ordSig, candidateFirst, false);
            return firstField != null && matchesFirstField(firstField);
        }

        public boolean matchesNextUsage(Expr candidateNext) {
            Sig.Field nextField = extractDottedField(ordSig, candidateNext, false);
            return nextField != null && matchesNextField(nextField);
        }

        public Term translateFirst(VarTuple tuple, TranslationContext context) {
            if (tuple.size() != 1) {
                throw new ErrorFatal("'first' is unary but used in a " + tuple.size() + "-ary context");
            }
            AnnotatedVar var = tuple.getAnnotatedVar(0);

            Sort sort = context.sortPolicy.getSort(sig);
            if (var.sort() != sort) {
                // Short-circuit: sorts are mismatched, can't be equal
                return Term.mkBottom();
            }

            // use the first in the range of domain elements
            Pair<Integer, Integer> range = context.sortPolicy.getDomainElementRange(sig, context.scoper);
            DomainElement firstDE = DomainElement.apply(range.a, sort);
            return Term.mkEq(var.variable(), firstDE);
        }

        public Term translateNext(VarTuple tuple, TranslationContext context) {
            if (tuple.size() != 2) {
                throw new ErrorFatal("'next' is binary but used in a " + tuple.size() + "-ary context");
            }

            // Short-circuit if the sorts are wrong
            Sort sort = context.sortPolicy.getSort(sig);
            if (tuple.getSort(0) != sort || tuple.getSort(1) != sort) {
                return Term.mkBottom();
            }

            // Lazily generate the actual Fortress function in case we don't need it
            ensureNextPredicateAdded(context);

            // Translate [[(x,y) \in next]] := [[x != last && next(x) = y]]
            // We check x != last because next(last) is left undefined
            Pair<Integer, Integer> range = context.sortPolicy.getDomainElementRange(sig, context.scoper);
            DomainElement lastDE = DomainElement.apply(range.b, sort);
            return Term.mkAnd(
                    Term.mkNot(Term.mkEq(tuple.getVar(0), lastDE)),
                    Term.mkEq(Term.mkApp(nextFuncName, tuple.getVar(0)), tuple.getVar(1)));
        }

        private void ensureNextPredicateAdded(TranslationContext context) {
            if (context.hasFunctionWithName(nextFuncName)) {
                return; // already exists
            }

            // Generate the function itself (next: sort->sort)
            Sort sort = context.sortPolicy.getSort(sig);
            FuncDecl funcDecl = FuncDecl.mkFuncDecl(nextFuncName, sort, sort);
            context.addFunctionDeclaration(funcDecl);

            // Constrain it by hardcoding the order, leaving next(last) undefined
            // Note: deRange is inclusive, so we exclude the last element in the range
            Pair<Integer, Integer> deRange = context.sortPolicy.getDomainElementRange(sig, context.scoper);
            for (int de = deRange.a; de < deRange.b; de++) {
                // "next(_@de) = _@(de+1)"
                Term axiom = Term.mkEq(
                        Term.mkApp(nextFuncName, DomainElement.apply(de, sort)),
                        DomainElement.apply(de + 1, sort));
                context.addAxiom(axiom);
            }
        }
    }

    private final List<OrderInfo> orders = new ArrayList<>();

    public OrderingModuleOptTranslator(Translator topLevel) {
        super(topLevel);
    }

    @Override
    public Term translate(Sig sig, TranslationContext context) {
        // Parse a "totalOrder" ExprList making up a fact.
        // We do this instead of just translating total orders normally to ensure we find all
        // ordering module uses before parsing the rest of the AST.
        for (Expr fact : sig.getFacts()) {
            fact = fact.deNOP(); // just in case
            if (fact instanceof ExprList && ((ExprList) fact).op == ExprList.Op.TOTALORDER) {
                parseTotalOrder(sig, (ExprList) fact, context);
            }
        }

        return null; // parse the actual sig by another translator
    }

    private void parseTotalOrder(Sig ordSig, ExprList expr, TranslationContext context) {
        // NOTE: we treat pred/totalOrder as an assertion that a sig is totally ordered.
        // Technically, since the Alloy AST isn't in NNF, this isn't necessarily true.
        // We ignore this for now since pred/totalOrder is probably only ever really used in ordering.als.

        // pred/totalOrder (TOTALORDER) is used like pred/totalOrder[OrderedSig, First, Next]
        // where OrderedSig is the sig being ordered, First is the first-element field, and Next is the next relation.
        // Make sure it's used correctly, then save First and Next.
        if (expr.args.size() != 3) {
            throw new ErrorFatal("pred/totalOrder must have 3 arguments: pred/totalOrder[Sig, First, Next]");
        }

        Expr orderedExpr = expr.args.get(0).deNOP();
        if (!(orderedExpr instanceof Sig.PrimSig)) {
            // TODO: should we support subset sigs? arbitrary expressions (Kodkod apparently does)?
            throw new ErrorFatal("Portus only supports ordering primitive signatures");
        }
        Sig.PrimSig orderedSig = (Sig.PrimSig) orderedExpr;

        // we expect "Ord.first" and "Ord.next"
        Sig.Field first = extractDottedField(ordSig, expr.args.get(1).deNOP(), true);
        Sig.Field next = extractDottedField(ordSig, expr.args.get(2).deNOP(), true);

        orders.add(new OrderInfo(ordSig, orderedSig, first, next, context));
    }

    private static Sig.Field extractDottedField(Sig ordSig, Expr expr, boolean shouldError) {
        if (!(expr instanceof ExprBinary) || ((ExprBinary) expr).op != ExprBinary.Op.JOIN) {
            if (shouldError) {
                throw new ErrorFatal("Expected join expression for second/third parameters of pred/totalOrder");
            }
            return null;
        }
        ExprBinary join = (ExprBinary) expr;
        if (!join.left.deNOP().isSame(ordSig) || !(join.right.deNOP() instanceof Sig.Field)) {
            if (shouldError) {
                throw new ErrorFatal("Expected Ord.first / Ord.next for second/third parameters of pred/totalOrder");
            }
            return null;
        }
        return (Sig.Field) join.right.deNOP();
    }

    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        // Intercept and ignore First and Next fields - we've handled them above
        for (OrderInfo order : orders) {
            if (order.matchesFirstField(field) || order.matchesNextField(field)) {
                return Term.mkTop(); // don't go to the next translator
            }
        }
        return null;
    }

    @Override
    public Term translate(ExprList expr, TranslationContext context) {
        // Don't error when we parse pred/totalOrder - just treat it as an assertion that it's a total order,
        // since we're making it a total order by the above, so just return true.
        if (expr.op == ExprList.Op.TOTALORDER) {
            return Term.mkTop();
        }
        return null;
    }

    @Override
    public Term translate(VarTuple tuple, ExprBinary expr, TranslationContext context) {
        // If it's a usage of any of the recognized first/next predicates, translate with it
        // (a "usage" is like Ord.First or Ord.Next)
        for (OrderInfo order : orders) {
            if (order.matchesFirstUsage(expr)) {
                return order.translateFirst(tuple, context);
            } else if (order.matchesNextUsage(expr)) {
                return order.translateNext(tuple, context);
            }
        }
        return null;
    }

    @Override
    public Term translate(VarTuple tuple, Sig.Field field, TranslationContext context) {
        // For visualization/XML, when First and Next are used outside "Ord.First"/"Ord.Next" expressions,
        // translate them directly by stripping the first element of the tuple (since that's the Ord one-sig)
        for (OrderInfo order : orders) {
            if (order.matchesFirstField(field)) {
                return order.translateFirst(tuple.slice(1, tuple.size()), context);
            } else if (order.matchesNextField(field)) {
                return order.translateNext(tuple.slice(1, tuple.size()), context);
            }
        }
        return null;
    }

}
