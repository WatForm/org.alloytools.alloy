package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.Sig;
import fortress.data.NameGenerator;
import fortress.msfol.DomainElement;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The ordering module optimization, where we hardcode a "next" function and a "first" element
 * for symmetry breaking.
 */
// TODO: implement Evaluator
final class OrderingModuleOptTranslator extends AbstractTranslator implements ScalarCaster {

    private final class OrderInfo {
        private final Sig ordSig;
        private final Sig.PrimSig sig;
        private final Sort sort;
        private final Sig.Field first;
        private final Sig.Field next;
        private final String nextFuncName;

        // The domain element corresponding to the one sig's only atom.
        private final DomainElement ordDE;

        public OrderInfo(Sig ordSig, Sig.PrimSig sig, Sig.Field first, Sig.Field next, TranslationContext context) {
            this.ordSig = ordSig;
            this.sig = sig;
            this.sort = sortPolicy.getSort(sig);
            this.first = first;
            this.next = next;
            this.nextFuncName = generateNextFuncName();
            validate(context);

            this.ordDE = PortusUtil.getOneSigDomainElement((Sig.PrimSig) ordSig, sortPolicy, context);
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
                throw new ErrorNoPortusSupport(
                        "Portus doesn't support ordering builtin signatures: " + sig.label);
            }
            if (sortPolicy.getSort(sig) == null) {
                throw new ErrorFatal("Sig " + sig.label + " can't be ordered because Portus can't determine a sort");
            }
            if (context.rangeAssigner.getDomainElementRange(sig) == null) {
                // this probably shouldn't happen
                throw new ErrorFatal("Sig " + sig.label + " can't be ordered for unknown reasons");
            }

            if (!PortusUtil.stripPortusNoops(first.decl().expr).isSame(sig.setOf())) {
                throw new ErrorNoPortusSupport(
                        "The First field in pred/totalOrder must be have the type of the ordered sig");
            }
            if (!PortusUtil.stripPortusNoops(next.decl().expr).isSame(sig.product(sig))) {
                throw new ErrorNoPortusSupport(
                        "The Next field in pred/totalOrder must have type S->S, where S is the ordered sig");
            }
        }

        public boolean matchesFirstField(Sig.Field candidateFirst) {
            return first.isSame(candidateFirst);
        }

        public boolean matchesNextField(Sig.Field candidateNext) {
            return next.isSame(candidateNext);
        }

        // Return a term saying that `term` matches the Ord one sig's single domain element.
        public Term getMatchesOrdDETerm(Term term, TranslationContext context) {
            // Add the range axiom here rather than in the constructor because ordSig hasn't been parsed by the
            // rest of the translators then, so translating [[@de \in ordSig]] will fail.
            // At this point ordSig has been run through all translators, so this is safe.
            context.rangeAssigner.addRangeAxiom(ordSig, topLevelTranslator, context);
            return Term.mkEq(term, ordDE);
        }

        public boolean matchesFirstUsage(Expr candidateFirst) {
            Sig.Field firstField = extractDottedField(ordSig, candidateFirst, false);
            return firstField != null && matchesFirstField(firstField);
        }

        public boolean matchesNextUsage(Expr candidateNext) {
            Sig.Field nextField = extractDottedField(ordSig, candidateNext, false);
            return nextField != null && matchesNextField(nextField);
        }

        public Expr getFirstUsage() {
            return ordSig.join(first);
        }

        public Expr getNextUsage() {
            return ordSig.join(next);
        }

        public AnnotatedTerm getFirstScalar(TranslationContext context) {
            // Use the first in the range of domain elements
            context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, context); // ensure range is valid
            Pair<Integer, Integer> range = context.rangeAssigner.getDomainElementRange(sig);
            return new AnnotatedTerm(Term.mkDomainElement(range.a, sort), sort);
        }

        public Scalar getNextScalar(TranslationContext context) {
            context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, context); // ensure range is valid
            Pair<Integer, Integer> range = context.rangeAssigner.getDomainElementRange(sig);
            DomainElement lastDE = Term.mkDomainElement(range.b, sort);

            // TODO: Short-circuit if it's a domain element?
            return new Scalar(Collections.singletonList(sort), sort,
                    tuple -> Term.mkApp(nextFuncName, tuple.getTerms()),
                    tuple -> Term.mkAnd(
                            recursivelyTranslate(ExprElementOf.make(tuple, sig), context),
                            Term.mkNot(Term.mkEq(tuple.getTerm(0), lastDE))));
        }

        public void addNextPredicate(TranslationContext context) {
            if (context.hasFunctionWithName(nextFuncName)) {
                return; // already exists
            }

            // Add a definition for next
            Sort sort = sortPolicy.getSort(sig);
            context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, context); // ensure range is valid

            if (useDefinition) {
                // Generate a lookup table for the definition body
                List<Pair<Term, Term>> lookupTable = new ArrayList<>();
                Pair<Integer, Integer> deRange = context.rangeAssigner.getDomainElementRange(sig);
                for (int de = deRange.a; de < deRange.b; de++) {
                    // "next(_@de) = _@(de+1)"
                    lookupTable.add(new Pair<>(Term.mkDomainElement(de, sort), Term.mkDomainElement(de + 1, sort)));
                }

                Var inputVar = Term.mkVar(nameGenerator.freshName("x"));
                Term lookupTableTerm;
                try {
                    context.addFortressVar(inputVar.of(sort));
                    if (lookupTable.isEmpty()) {
                        // The ordered sig has a scope of 1, so every value of next is ignored.
                        // This is an edge case so don't bother optimizing specially - assign it arbitrarily.
                        lookupTableTerm = Term.mkDomainElement(deRange.a, sort);
                    } else {
                        lookupTableTerm = PortusUtil.mkExhaustiveLookupTable(inputVar, lookupTable);
                    }
                } finally {
                    context.removeFortressVar(inputVar.of(sort));
                }
                FunctionDefinition definition = FunctionDefinition.mkFunctionDefinition(
                        nextFuncName, Collections.singletonList(inputVar.of(sort)), sort, lookupTableTerm);
                context.addFunctionDefinition(definition);
            } else {
                // Generate the function (next: sort->sort)
                FuncDecl funcDecl = FuncDecl.mkFuncDecl(nextFuncName, sort, sort);
                context.addFunctionDeclaration(funcDecl);

                // Constrain it by hardcoding the order, leaving next(last) undefined
                // Note: deRange is inclusive, so we exclude the last element in the range
                context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, context); // ensure range is valid
                Pair<Integer, Integer> deRange = context.rangeAssigner.getDomainElementRange(sig);
                for (int de = deRange.a; de < deRange.b; de++) {
                    // "next(_@de) = _@(de+1)"
                    Term axiom = Term.mkEq(
                            Term.mkApp(nextFuncName, Term.mkDomainElement(de, sort)),
                            Term.mkDomainElement(de + 1, sort));
                    context.addAxiom(axiom);
                }
            }
        }
    }

    private final List<OrderInfo> orders = new ArrayList<>();

    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    private final boolean useDefinition;

    public OrderingModuleOptTranslator(
            Translator topLevel, SortPolicy sortPolicy, NameGenerator nameGenerator, boolean useDefinition) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.useDefinition = useDefinition;
    }

    @Override
    public String name() {
        return "Ordering Module Optimization";
    }

    /**
     * This pass should run before the main translation pass.
     * It marks all sigs that are ever ordered in the context so that other translators know which
     * sigs will be ordered.
     */
    public Pass getMarkOrderedSigsPass() {
        return (world, command, scoper, context) -> {
            // Mark all sigs that are ever ordered by any Ord sig.
            for (Sig sig : world.getAllReachableSigs()) {
                for (Expr fact : sig.getFacts()) {
                    fact = fact.deNOP();
                    if (isTotalOrderFact(fact)) {
                        OrderInfo orderInfo = parseTotalOrder(sig, (ExprList) fact, context);
                        context.setSigOrdered(orderInfo.sig);
                    }
                }
            }
        };
    }

    private boolean isAnyParentOrdered(Sig.PrimSig sig) {
        return !sig.isTopLevel() && (orders.stream().anyMatch(order -> order.sig.equals(sig.parent))
                || isAnyParentOrdered(sig.parent));
    }

    private boolean violatesNoMultiLevelOrdering(Sig.PrimSig sig) {
        // sig violates the rule against no multi-level orderings iff sig has an ordered ancestor or sig is an
        // ancestor of any other ordered sig
        return isAnyParentOrdered(sig) || orders.stream().anyMatch(
                order -> PortusUtil.isAncestorSig(sig, order.sig));
    }

    @Override
    public Term translate(Sig sig, TranslationContext context) {
        // Parse a "totalOrder" ExprList making up a fact.
        // We do this instead of just translating total orders normally to ensure we find all
        // ordering module uses before parsing the rest of the AST.
        for (Expr fact : sig.getFacts()) {
            fact = fact.deNOP(); // just in case
            if (isTotalOrderFact(fact)) {
                OrderInfo orderInfo = parseTotalOrder(sig, (ExprList) fact, context);

                // We don't support ordering both a signature and its ancestor because that would fix a relationship
                // between the orderings, resulting in a loss of generality.
                if (violatesNoMultiLevelOrdering(orderInfo.sig)) {
                    throw new ErrorNoPortusSupport(
                            "Multiple levels of the signature hierarchy cannot be simultaneously ordered.");
                }
                orders.add(orderInfo);

                // Add the predicate immediately instead of lazily - if we do it lazily and don't end up adding it,
                // then when we go to evaluate ordering/Ord.Next, we get errors since the predicate doesn't exist.
                orderInfo.addNextPredicate(context);
            }
        }

        return null; // parse the actual sig by another translator
    }

    private boolean isTotalOrderFact(Expr fact) {
        return fact instanceof ExprList && ((ExprList) fact).op == ExprList.Op.TOTALORDER;
    }

    private OrderInfo parseTotalOrder(Sig ordSig, ExprList expr, TranslationContext context) {
        // NOTE: we treat pred/totalOrder as an assertion that a sig is totally ordered.
        // Technically, since the Alloy AST isn't in NNF, this isn't necessarily true.
        // We ignore this for now since pred/totalOrder is probably only ever really used in ordering.als.

        // pred/totalOrder (TOTALORDER) is used like pred/totalOrder[OrderedSig, First, Next]
        // where OrderedSig is the sig being ordered, First is the first-element field, and Next is the next relation.
        // Make sure it's used correctly, then save First and Next.
        if (expr.args.size() != 3) {
            throw new ErrorNoPortusSupport(
                    "pred/totalOrder must have 3 arguments: pred/totalOrder[Sig, First, Next]");
        }

        Expr orderedExpr = expr.args.get(0).deNOP();
        if (!(orderedExpr instanceof Sig.PrimSig)) {
            // TODO: should we support subset sigs? arbitrary expressions (Kodkod apparently does)?
            throw new ErrorNoPortusSupport("Portus only supports ordering primitive signatures");
        }
        Sig.PrimSig orderedSig = (Sig.PrimSig) orderedExpr;

        // we expect "Ord.first" and "Ord.next"
        Sig.Field first = extractDottedField(ordSig, expr.args.get(1).deNOP(), true);
        Sig.Field next = extractDottedField(ordSig, expr.args.get(2).deNOP(), true);

        return new OrderInfo(ordSig, orderedSig, first, next, context);
    }

    private static Sig.Field extractDottedField(Sig ordSig, Expr expr, boolean shouldError) {
        expr = PortusUtil.stripPortusNoops(expr);
        if (!(expr instanceof ExprBinary) || ((ExprBinary) expr).op != ExprBinary.Op.JOIN) {
            if (shouldError) {
                throw new ErrorNoPortusSupport(
                        "Expected join expression for second/third parameters of pred/totalOrder");
            }
            return null;
        }
        ExprBinary join = (ExprBinary) expr;
        if (!PortusUtil.stripPortusNoops(join.left).isSame(ordSig)
                || !(PortusUtil.stripPortusNoops(join.right) instanceof Sig.Field)) {
            if (shouldError) {
                throw new ErrorNoPortusSupport(
                        "Expected Ord.First / Ord.Next for second/third parameters of pred/totalOrder");
            }
            return null;
        }
        return (Sig.Field) PortusUtil.stripPortusNoops(join.right);
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
    public Term translate(TermTuple tuple, Sig.Field field, TranslationContext context) {
        // For visualization/XML, when First and Next are used outside "Ord.First"/"Ord.Next" expressions,
        // translate them directly by stripping the first element of the tuple (since that's the Ord one-sig),
        // and also check that the first element of the tuple is the Ord sig's one atom
        for (OrderInfo order : orders) {
            Term matchesOrdDE = order.getMatchesOrdDETerm(tuple.getTerm(0), context);
            if (order.matchesFirstField(field)) {
                return Term.mkAnd(matchesOrdDE, recursivelyTranslate(
                        ExprElementOf.make(tuple.slice(1, tuple.size()), order.getFirstUsage()), context));
            } else if (order.matchesNextField(field)) {
                return Term.mkAnd(matchesOrdDE, recursivelyTranslate(
                        ExprElementOf.make(tuple.slice(1, tuple.size()), order.getNextUsage()), context));
            }
        }
        return null;
    }

    /** Cast first and next to scalars. */
    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        expr = PortusUtil.stripPortusNoops(expr);

        for (OrderInfo order : orders) {
            if (order.matchesFirstUsage(expr)) {
                // No guard is necessary since it's a plain domain element.
                return new Scalar(order.getFirstScalar(context), Term.mkTop());
            } else if (order.matchesNextUsage(expr)) {
                return order.getNextScalar(context);
            }
        }
        return null;
    }

}
