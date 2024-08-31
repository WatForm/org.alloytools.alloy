package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import fortress.data.NameGenerator;
import fortress.msfol.AndList;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.App;
import fortress.msfol.BitVectorLiteral;
import fortress.msfol.BuiltinApp;
import fortress.msfol.Closure;
import fortress.msfol.ConstantDefinition;
import fortress.msfol.Distinct;
import fortress.msfol.DomainElement;
import fortress.msfol.EnumValue;
import fortress.msfol.Eq;
import fortress.msfol.Exists;
import fortress.msfol.Forall;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.IfThenElse;
import fortress.msfol.Iff;
import fortress.msfol.Implication;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Not;
import fortress.msfol.OrList;
import fortress.msfol.Quantifier;
import fortress.msfol.ReflexiveClosure;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.TermVisitor;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.msfol.Var;
import fortress.operations.Substituter;
import fortress.operations.TermOps;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * General-purpose utility functions used in Portus.
 */
final class PortusUtil {

    private PortusUtil() {}

    /** Convert a java.util.Map to a scala.collection.immutable.Map. */
    public static <A, B> scala.collection.immutable.Map<A, B> toScalaMap(Map<A, B> map) {
        //noinspection unchecked
        return scala.collection.immutable.Map.from(CollectionConverters.asScala(map));
    }

    /** Strip wrappers we consider to be (pure) NOOPs: CAST2INT, CAST2SIGINT, NOOP. */
    public static Expr stripPortusNoops(Expr expr) {
        while (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            if (unary.op == ExprUnary.Op.NOOP
                || unary.op == ExprUnary.Op.CAST2INT
                || unary.op == ExprUnary.Op.CAST2SIGINT) {
                expr = unary.sub;
            } else {
                break;
            }
        }
        return expr;
    }

    /**
     * Software Abstractions, sec. 3.6.4: a "declaration formula" is a expression of the form
     * "a in b M->N c", where M and N are multiplicities, or b or c are arrow-expressions with
     * multiplicities. Return whether expr is a declaration formula.
     */
    public static boolean isDeclarationFormula(Expr expr) {
        if (!(expr instanceof ExprBinary)) return false;
        ExprBinary inExpr = (ExprBinary) expr;
        if (inExpr.op != ExprBinary.Op.IN) return false;
        return isDeclarationFormulaArrow(inExpr.right.deNOP());
    }

    /**
     * Return whether expr is the arrow expression from a declaration formula.
     */
    public static boolean isDeclarationFormulaArrow(Expr expr) {
        if (!(expr instanceof ExprBinary)) return false;
        ExprBinary arrow = (ExprBinary) expr;
        // mult == 2 means "has an arrow multiplicity constraint"
        return arrow.op.isArrow && arrow.mult == 2;
    }

    /**
     * Throw an error if the literal integer value is outside the valid integer range for the bitwidth.
     * This is used because Fortress's OPFI enforces the integer range more strictly than Kodkod.
     */
    public static void checkLiteralIntWithinBitwidth(int literalValue, int bitwidth) {
        if (literalValue < Util.min(bitwidth) || literalValue > Util.max(bitwidth)) {
            throw new ErrorNoPortusSupport(
                    "Integer literal " + literalValue + " is outside the valid integer range at bitwidth " + bitwidth
                    + "! Please increase the bitwidth or modify your model.");
        }
    }

    /**
     * Return the unary multiplicity operator corresponding to "M" in "M->N", or NOOP if
     * there's no multiplicity operator. Return null if arrowOp isn't an arrow operator.
     */
    @SuppressWarnings("DuplicatedCode") // IntelliJ's duplication detection is a little aggressive
    public static ExprUnary.Op getArrowLeftMultiplicity(ExprBinary.Op arrowOp) {
        if (!arrowOp.isArrow) return null;

        switch (arrowOp) {
            case ONE_ARROW_ANY:
            case ONE_ARROW_ONE:
            case ONE_ARROW_LONE:
            case ONE_ARROW_SOME:
                return ExprUnary.Op.ONE;
            case LONE_ARROW_ANY:
            case LONE_ARROW_ONE:
            case LONE_ARROW_LONE:
            case LONE_ARROW_SOME:
                return ExprUnary.Op.LONE;
            case SOME_ARROW_ANY:
            case SOME_ARROW_ONE:
            case SOME_ARROW_LONE:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOME;
            default:
                return ExprUnary.Op.NOOP;
        }
    }

    /**
     * Return the unary multiplicity operator corresponding to "N" in "M->N", or NOOP if
     * there's no multiplicity operator. Return null if arrowOp isn't an arrow operator.
     */
    @SuppressWarnings("DuplicatedCode")
    public static ExprUnary.Op getArrowRightMultiplicity(ExprBinary.Op arrowOp) {
        if (!arrowOp.isArrow) return null;

        switch (arrowOp) {
            case ANY_ARROW_ONE:
            case ONE_ARROW_ONE:
            case LONE_ARROW_ONE:
            case SOME_ARROW_ONE:
                return ExprUnary.Op.ONE;
            case ANY_ARROW_LONE:
            case ONE_ARROW_LONE:
            case LONE_ARROW_LONE:
            case SOME_ARROW_LONE:
            case ISSEQ_ARROW_LONE:
                return ExprUnary.Op.LONE;
            case ANY_ARROW_SOME:
            case ONE_ARROW_SOME:
            case LONE_ARROW_SOME:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOME;
            default:
                return ExprUnary.Op.NOOP;
        }
    }

    /**
     * Remove all multiplicities like M and N in "A M->N B", as well as nested multiplicities.
     * If it's not an arrow ExprBinary, return it unchanged.
     */
    public static Expr stripArrowMultiplicities(Expr expr) {
        if (!(expr instanceof ExprBinary)) return expr;
        ExprBinary arrow = (ExprBinary) expr;
        if (!arrow.op.isArrow) return arrow;
        // recurse to strip nested multiplicities
        return stripArrowMultiplicities(arrow.left).product(stripArrowMultiplicities(arrow.right));
    }

    /**
     * Is `ancestor` an ancestor of `sig` in the signature hierarchy?
     */
    public static boolean isAncestorSig(Sig.PrimSig ancestor, Sig.PrimSig sig) {
        return sig.equals(ancestor) || (!sig.isTopLevel() && isAncestorSig(ancestor, sig.parent));
    }

    /**
     * Given a one sig, return the domain element corresponding to its single atom. The context is used
     * to assign the domain element, which is the first/only one in its domain element range.
     * {@link RangeAssigner#addRangeAxiom(Sig, Translator, TranslationContext)} must still be used to ensure
     * the domain element is actually assigned to the sig.
     */
    public static DomainElement getOneSigDomainElement(
            Sig.PrimSig sig, SortPolicy sortPolicy, TranslationContext context) {
        if (sig.isOne == null) {
            throw new IllegalArgumentException("getOneSigDomainElement expects a one sig");
        }
        Pair<Integer, Integer> deRange = context.rangeAssigner.getDomainElementRange(sig);
        Sort sort = sortPolicy.getSort(sig);
        if (deRange == null || sort == null) {
            throw new ErrorFatal("Portus error: one sig " + sig + " has null domain element range or sort");
        }
        if (!Objects.equals(deRange.a, deRange.b)) {
            throw new ErrorFatal(
                    "Internal Portus error: one sig " + sig + " has non-one range " + deRange.a + "," + deRange.b);
        }
        return Term.mkDomainElement(deRange.a, sort);
    }

    /**
     * Translate a list of decls from a quantifier.
     * @return Pair of (pair of (list of mapped Alloy variable names, list of Fortress vars), condition),
     *   where the condition expresses that each variable is in the expr the decl declares it to be in.
     *   The condition must be true for the variables to be used.
     * @apiNote The variable names are added to the context's var mapping and must be cleaned up after.
     * This should be done by removing each of the list of mapped Alloy variable names from the context.
     * We assume that none of the decls' expressions resolve to "none" (i.e. their sort resolvants are empty).
     * This must be handled at a higher level.
     */
    public static Pair<Pair<List<String>, List<AnnotatedVar>>, AnnotatedTerm> translateDeclList(
            List<Decl> decls, TranslationContext context, SortPolicy sortPolicy, Translator rootTranslator,
            NameGenerator nameGenerator) {
        List<String> alloyVarNames = new ArrayList<>();
        List<AnnotatedVar> fortressVars = new ArrayList<>();
        List<Term> conditions = new ArrayList<>();

        for (Decl decl : decls) {
            // Kodkod evaluates the decl expression once. To emulate this, only add the
            // variables to the context after evaluating the whole decl.
            List<Pair<String, AnnotatedTerm>> termMappingsToAdd = new ArrayList<>();
            List<AnnotatedVar> fortressVarsToAdd = new ArrayList<>();

            // Alloy typechecked that it has arity 1
            for (ExprHasName name : decl.names) {
                // Ensure decl.expr is ONEOF: we don't support other multiplicities in quantifiers (yet)
                // TODO: try to skolemize it like Kodkod does?
                ExprUnary.Op mult = decl.expr.mult();
                if (mult != ExprUnary.Op.ONEOF) {
                    // Treat "no multiplicity" as ONEOF because Alloy sometimes generates those internally.
                    // mult() generates SETOF for no multiplicity, so check that either the expr isn't actually
                    // an ExprUnary or it's an ExprUnary with a different op.
                    boolean noMultiplicity = mult == ExprUnary.Op.SETOF
                            && (!(decl.expr.deNOP() instanceof ExprUnary)
                            || ((ExprUnary) decl.expr.deNOP()).op != ExprUnary.Op.SETOF);
                    if (!noMultiplicity) {
                        throw new ErrorNoPortusSupport("Unsupported quantifier multiplicity for Fortress: "
                                + decl.expr.mult());
                    }
                }

                // Unwrap the expression from its multiplicity (and any NOOPs)
                Expr declExpr = decl.expr.deNOP();
                if (declExpr instanceof ExprUnary) {
                    ExprUnary wrappedDeclExpr = (ExprUnary) decl.expr.deNOP();
                    if (wrappedDeclExpr.op == ExprUnary.Op.ONEOF) {
                        declExpr = wrappedDeclExpr.sub.deNOP();
                    }
                }

                Var var = Term.mkVar(nameGenerator.freshName(name.label));
                // Note that the decl expr has to be unary since typechecking should have caught anything else
                String definiteSortsError = "Translating a quantification requires the variable declarations " +
                        "to have definite and well-defined Portus sorts!";
                List<Sort> exprSorts = sortPolicy.getMinimalExprDefiniteSorts(declExpr, definiteSortsError, context);
                if (exprSorts.size() != 1) {
                    // Could happen for cases Kodkod skolemizes, like e.g. "some s: one A->B | ..."
                    // Also occurs e.g. with "pred foo[s: A->B] {...}; run foo" since that runs "some s: A->B | foo[s]"
                    throw new ErrorNoPortusSupport("Portus doesn't support quantifying over tuples!");
                }
                Sort varSort = exprSorts.get(0);
                AnnotatedVar annotatedVar = var.of(varSort);
                alloyVarNames.add(name.label);
                fortressVarsToAdd.add(annotatedVar);

                try {
                    // Add the condition "var \in declExpr" to restrict the domain of var
                    context.addFortressVar(annotatedVar);
                    Expr domainExpr = ExprElementOf.make(annotatedVar, declExpr);
                    conditions.add(rootTranslator.translate(domainExpr, context));
                } finally {
                    context.removeFortressVar(annotatedVar);
                }

                // Add it to the lexical scope to translate the subformula
                termMappingsToAdd.add(new Pair<>(name.label, new AnnotatedTerm(annotatedVar)));
            }

            // Add the term mappings and fortress vars now, in order, after having translated the decl expression
            for (Pair<String, AnnotatedTerm> mapping : termMappingsToAdd) {
                context.addTermMapping(mapping.a, mapping.b);
            }
            context.addFortressVars(fortressVarsToAdd);
            fortressVars.addAll(fortressVarsToAdd);
        }

        // All the conditions must be true for a set of variables to be used
        Term condition = conditions.isEmpty() ? Term.mkTop() : Term.mkAnd(conditions);
        AnnotatedTerm conditionAnnotated = new AnnotatedTerm(condition, Sort.Bool());
        return new Pair<>(new Pair<>(alloyVarNames, fortressVars), conditionAnnotated);
    }

    /**
     * For each pair of vars (v1, v2) in zip(a, b), substitute v1 -> v2 in term.
     * We require that a and b have the same size.
     */
    public static Term substituteVars(List<AnnotatedVar> a, List<AnnotatedVar> b, Term term) {
        return substitute(a, b.stream().map(AnnotatedVar::variable).collect(Collectors.toList()), term);
    }

    /**
     * For each (var, term) pair (v, t) in zip(a, b), substitute v -> t in term.
     * We require that a and b have the same size.
     */
    public static Term substitute(List<AnnotatedVar> a, List<? extends Term> b, Term term) {
        if (a.size() != b.size()) {
            throw new IllegalArgumentException("a and b must have same size");
        }

        // TODO: can we use FastSubstituter in some cases?
        NameGenerator nameGen = new SanitizingNameGenerator();
        for (int i = 0; i < a.size(); i++) {
            Var from = a.get(i).variable();
            Term to = b.get(i);
            term = Substituter.apply(from, to, term, nameGen);
        }
        return term;
    }

    /**
     * Generate the term (v1 = u1) && (v2 = u2) && ... && (vn = un) for each pair
     * (vi, ui) in zip(a, b). We require that a and b have the same size.
     */
    public static Term mkVarsEqual(List<AnnotatedVar> a, List<AnnotatedVar> b) {
        if (a.size() != b.size()) {
            throw new IllegalArgumentException("a and b must have same size");
        }
        List<Term> conjuncts = new ArrayList<>();
        for (int i = 0; i < a.size(); i++) {
            conjuncts.add(Term.mkEq(a.get(i).variable(), b.get(i).variable()));
        }
        return Term.mkAnd(conjuncts);
    }

    public static Term mkExhaustiveLookupTable(Term input, List<Pair<Term, Term>> table) {
        if (table.isEmpty()) {
            throw new IllegalArgumentException("Cannot make an empty exhaustive lookup table!");
        }
        Term firstKey = table.get(0).a;
        Term firstValue = table.get(0).b;
        if (table.size() == 1) {
            // it's exhaustive, so don't both checking the key
            return firstValue;
        }
        return Term.mkIfThenElse(Term.mkEq(input, firstKey), firstValue,
                mkExhaustiveLookupTable(input, table.subList(1, table.size())));
    }

    /**
     * Given a current list of integers [x1,...,xn] and a list of maximums [m1,...,mn],
     * mutate current to the next element in the Cartesian product {1,...,m1}x...x{1,...,mn}.
     * Return true if we got a new combination or false if current is the last combination.
     */
    public static boolean nextCombination(List<Integer> current, List<Integer> max) {
        if (current.size() != max.size()) {
            throw new IllegalArgumentException("current and max must have the same size");
        }
        for (int i = max.size() - 1; i >= 0; i--) {
            if (current.get(i) < max.get(i)) {
                current.set(i, current.get(i) + 1);
                return true;
            } else {
                current.set(i, 1);
            }
        }
        return false;
    }

    /**
     * Given a list of sorts, call the callback for every tuple of values in the cross product of the sorts.
     */
    public static void expandOverSorts(List<Sort> sorts, SortPolicy sortPolicy, Consumer<List<Value>> callback) {
        List<Integer> sortScopes = new ArrayList<>();
        List<Integer> currentIdxs = new ArrayList<>();
        for (Sort sort : sorts) {
            sortScopes.add(sortPolicy.getSortScope(sort));
            currentIdxs.add(1);
        }

        do {
            List<Value> tuple = IntStream.range(0, sorts.size())
                    // Subtract 1 because getElement expects 0-indexed but we generate 1-indexed
                    .mapToObj(i -> getElement(currentIdxs.get(i) - 1, sorts.get(i)))
                    .collect(Collectors.toList());
            callback.accept(tuple);
        } while (nextCombination(currentIdxs, sortScopes));
    }

    /**
     * Get the idx'th element of sort, where idx is in [0, scope of sort - 1].
     * This handles integers properly.
     */
    public static Value getElement(int idx, Sort sort) {
        if (sort.equals(Sort.Int())) {
            // Cleverly do it without the bitwidth by mapping 0, 1, 2, ... to 0, -1, 1, -2, 2, -3, 3, ...
            // Cutting off the first 2^n terms in this sequence yields the range [-2^{n-1}, 2^{n-1}-1].
            // This bijection maps 2n to n and 2n+1 to -(n+1).
            int integer;
            if (idx % 2 == 0) {
                integer = idx/2;
            } else {
                integer = -(idx+1)/2;
            }
            return IntegerLiteral.apply(integer);
        } else if (sort.isBuiltin()) {
            throw new ErrorFatal("Cannot get element of builtin non-Int sort: " + sort);
        }
        // Convert to 1-indexed from 0-indexed
        return Term.mkDomainElement(idx + 1, sort);
    }

    /**
     * Convert an iterable to a list. Java doesn't make this as easy as it should be.
     */
    public static <T> List<T> iterableToList(Iterable<T> iterable) {
        List<T> list = new ArrayList<>();
        iterable.forEach(list::add);
        return list;
    }

    /**
     * Get a list of the variables which are free in the translation of expr, with sorts determined by the context
     * (which should assign a Fortress var for each free Alloy var).
     * Order is deterministic.
     */
    public static List<AnnotatedVar> computeFreeVariables(
            Expr expr, TranslationContext context, SortPolicy sortPolicy) {
        // simple recursive implementation
        return expr.accept(new ContextVisitReturn<List<AnnotatedVar>>(context.varMappingContext, sortPolicy) {
            @SafeVarargs
            private final List<AnnotatedVar> union(List<AnnotatedVar>... lists) {
                // this is O(n^2) to union two lists of length n, but this shouldn't be a bottleneck
                List<AnnotatedVar> result = new ArrayList<>();
                for (List<AnnotatedVar> list : lists) {
                    for (AnnotatedVar var : list) {
                        if (!result.contains(var)) {
                            result.add(var);
                        }
                    }
                }
                return result;
            }

            @Override
            public List<AnnotatedVar> visit(ExprBinary x) throws Err {
                return union(visitThis(x.left), visitThis(x.right));
            }

            @Override
            public List<AnnotatedVar> visit(ExprList x) throws Err {
                //noinspection unchecked
                return union(x.args.stream()
                        .map(this::visitThis)
                        .toArray(List[]::new));
            }

            @Override
            public List<AnnotatedVar> visit(ExprCall x) throws Err {
                //noinspection unchecked
                return union(x.args.stream()
                        .map(this::visitThis)
                        .toArray(List[]::new));
            }

            @Override
            public List<AnnotatedVar> visit(ExprConstant x) throws Err {
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(ExprITE x) throws Err {
                return union(visitThis(x.cond), visitThis(x.left), visitThis(x.right));
            }

            @Override
            public List<AnnotatedVar> visitLet(ExprLet x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public List<AnnotatedVar> visitQuantifier(
                    ExprQt x, List<List<AnnotatedVar>> argResults, boolean anyArgNone) throws Err {
                if (anyArgNone) {
                    // don't recurse - any free variables won't be translated anyways
                    return new ArrayList<>();
                }

                // the special bound variable represents vars that aren't free - remove it from the list
                List<AnnotatedVar> freeVars = argResults.stream().reduce(new ArrayList<>(), this::union);
                List<AnnotatedVar> subFreeVars = visitThis(x.sub);
                return union(freeVars, subFreeVars).stream()
                        .filter(var -> !isPlaceholderBoundVar(var.variable()))
                        .collect(Collectors.toList());
            }

            @Override
            public List<AnnotatedVar> visitQuantifierArg(Expr arg) throws Err {
                // Translate quantifier arguments normally (in proper context) so we can union the result
                return visitThis(arg);
            }

            @Override
            public List<AnnotatedVar> visit(ExprUnary x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public List<AnnotatedVar> visitVar(ExprVar x) throws Err {
                // Let mappings are handled for us, so it should be in the context - use it
                if (!varMappingContext.hasTermMapping(x.label)) {
                    throw new ErrorFatal("Unknown variable: " + x.label);
                }
                AnnotatedTerm mappedTerm = varMappingContext.getTermMapping(x.label);
                assert mappedTerm != null;
                return computeTermFreeVars(mappedTerm.getTerm(), context);
            }

            @Override
            public List<AnnotatedVar> visit(Sig sig) throws Err {
                // sigs aren't variables
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(Sig.Field x) throws Err {
                // fields aren't variables
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(ExprElementOf x) throws Err {
                return union(x.tuple.getAllFreeVars(context), visitThis(x.sub));
            }

            @Override
            public List<AnnotatedVar> visit(Func x) throws Err {
                throw new ErrorFatal("Visiting Func isn't supported!");
            }

            @Override
            public List<AnnotatedVar> visit(Assert x) throws Err {
                throw new ErrorFatal("Visiting Assert isn't supported!");
            }

            @Override
            public List<AnnotatedVar> visit(Macro macro) throws Err {
                throw new ErrorFatal("Visiting Macro isn't supported!");
            }
        });
    }

    public static List<AnnotatedVar> computeTermFreeVars(Term term, TranslationContext context) {
        //noinspection unchecked
        List<Var> freeVars = CollectionConverters.<Var> asJava(
                TermOps.wrapTerm(term).freeVars(context.getTheory().signature()).toList());
        List<AnnotatedVar> annotatedFreeVars = new ArrayList<>(freeVars.size());
        for (Var var : freeVars) {
            if (context.hasConstantWithName(var.name())) {
                // constants aren't free variables
                continue;
            }
            if (!context.isFortressVarKnown(var)) {
                throw new ErrorFatal("Internal Portus error: sort of var " + var.name() + " unknown!");
            }
            annotatedFreeVars.add(new AnnotatedVar(var, context.getFortressVarSort(var)));
        }
        return annotatedFreeVars;
    }

    /**
     * Expand all the 'let's in an expression, for use when disambiguating expressions.
     */
    public static Expr expandLets(Expr expr, VarMappingContext varMappingContext, SortPolicy sortPolicy) {
        // note: this is vulnerable to exponential blowup in cases like
        // let x1=A+A | let x2=x1+x1 | let x3=x2+x2 | ... | let x64=x63+x63 | f[x64]
        // which will cause us to generate a union of 2^64 A's (!!)
        // but let's assume our users aren't evil enough to do that, eh?
        return expr.accept(new ContextVisitReturn<Expr>(varMappingContext, sortPolicy) {
            @Override
            public Expr visit(ExprBinary x) throws Err {
                return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visit(ExprList x) throws Err {
                return ExprList.make(x.pos, x.closingBracket, x.op, x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()));
            }

            @Override
            public Expr visit(ExprCall x) throws Err {
                // Don't expand ExprCalls for now - this might cause us to generate some duplicate auxiliary
                // functions when translating closure, e.g.
                //   ^x   and    ^f[x] where fun f[y] { y }
                // will generate two different auxiliary functions, but that's okay
                return ExprCall.make(null, null, x.fun, x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()), x.extraWeight);
            }

            @Override
            public Expr visit(ExprConstant x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprITE x) throws Err {
                return ExprITE.make(x.pos, visitThis(x.cond), visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visitLet(ExprLet x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public Expr visitQuantifier(ExprQt x, List<Expr> argResults, boolean anyArgNone) throws Err {
                // It's okay for us to ignore anyArgNone because we don't care if the ExprVars we meet
                // in recursion are in the context or not (if they aren't in let).
                // TODO: Could we just not recurse here if anyArgNone is true?
                // TODO: Possibility for bug due to conflict between let and none vars?
                List<Decl> decls = x.decls.stream().map(decl -> new Decl(
                        decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar, decl.names, visitThis(decl.expr)))
                        .collect(Collectors.toList());
                return x.op.make(x.pos, x.closingBracket, decls, visitThis(x.sub));
            }

            @Override
            public Expr visit(ExprUnary x) throws Err {
                return x.op.make(x.pos, visitThis(x.sub));
            }

            @Override
            public Expr visitVar(ExprVar x) throws Err {
                // expansion was performed by ContextVisitReturn
                return x;
            }

            @Override
            public Expr visit(Sig sig) throws Err {
                return sig;
            }

            @Override
            public Expr visit(Sig.Field x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprElementOf x) throws Err {
                return ExprElementOf.make(x.tuple, visitThis(x.sub));
            }

            @Override
            public Expr visit(Func x) throws Err {
                throw new ErrorFatal("Visiting Func isn't supported!");
            }

            @Override
            public Expr visit(Assert x) throws Err {
                throw new ErrorFatal("Visiting Assert isn't supported!");
            }

            @Override
            public Expr visit(Macro macro) throws Err {
                throw new ErrorFatal("Visiting Macro isn't supported!");
            }
        });
    }

    /**
     * Compare a and b for syntactically equality. See
     * {@link #areExprsEqual(Expr, Expr, VarMappingContext, VarMappingContext)}, without the context complications.
     * No variables are dereferenced.
     */
    public static boolean areExprsEqual(Expr a, Expr b) {
        return areExprsEqual(a, b, null, null);
    }

    /**
     * Determine whether a and b are syntactically equal for our purposes.
     * This does not take into account contexts -- free variables may have different meanings in a and b
     * if they are from different contexts, even if they are syntactically equal.
     * Does not do any commutativity simplification: x && y is not equal to y && x, and all x, y: A | f
     * is not equal to all y, x: A | f.
     * If the var mapping contexts are not null, use it to dereference term mappings only: that is,
     * if a's var mapping context maps the Alloy variable x to a Fortress term f and b's maps y to f, then
     * x and y compare equal.
     * If the var mapping contexts *are* null, all free variables are compared purely syntactically.
     * Note that let mappings are never dereferenced. If you want let mappings to be dereferenced,
     * expand with expandLets() first.
     * TODO: This is far too complicated, refactor.
     */
    public static boolean areExprsEqual(Expr a, Expr b, VarMappingContext contextA, VarMappingContext contextB) {
        // Either both or neither context must be null.
        if ((contextA == null) != (contextB == null)) {
            throw new IllegalStateException("areExprsEqual: both or neither contexts must be null");
        }

        if (a == null || b == null) {
            return a == null && b == null;
        }

        Expr strippedA = PortusUtil.stripPortusNoops(a);
        Expr strippedB = PortusUtil.stripPortusNoops(b);

        // Unfortunately, isSame() isn't implemented consistently, so we have to do this.
        return new FortressVisitReturn<Boolean>() {
            private boolean areDeclsEqual(Decl x, Decl y) {
                return x.names.size() == y.names.size()
                        && IntStream.range(0, x.names.size())
                            .allMatch(idx -> areExprsEqual(x.names.get(idx), y.names.get(idx)))
                        && areExprsEqual(x.expr, y.expr);
            }

            private boolean areDeclListsEqual(List<Decl> x, List<Decl> y) {
                return x.size() == y.size() && IntStream.range(0, x.size())
                        .allMatch(idx -> areDeclsEqual(x.get(idx), y.get(idx)));
            }

            private boolean areExprListsEqual(List<Expr> x, List<Expr> y) {
                return x.size() == y.size() && IntStream.range(0, x.size())
                        .allMatch(idx -> areExprsEqual(x.get(idx), y.get(idx)));
            }

            @Override
            public Boolean visit(ExprElementOf x) throws Err {
                if (!(strippedB instanceof ExprElementOf)) return false;
                ExprElementOf y = (ExprElementOf) strippedB;

                // Require syntactic equality on the LHS and then recurse on the RHS
                return x.tuple.equals(y.tuple) && areExprsEqual(x.sub, y.sub);
            }

            @Override
            public Boolean visit(ExprBinary x) throws Err {
                if (!(strippedB instanceof ExprBinary)) return false;
                ExprBinary y = (ExprBinary) strippedB;
                return x.op == y.op
                        && areExprsEqual(x.left, y.left)
                        && areExprsEqual(x.right, y.right);
            }

            @Override
            public Boolean visit(ExprList x) throws Err {
                if (!(strippedB instanceof ExprList)) return false;
                ExprList y = (ExprList) strippedB;
                return x.op == y.op && areExprListsEqual(x.args, y.args);
            }

            @Override
            public Boolean visit(ExprCall x) throws Err {
                if (!(strippedB instanceof ExprCall)) return false;
                ExprCall y = (ExprCall) strippedB;
                return areExprsEqual(x.fun, y.fun) && areExprListsEqual(x.args, y.args);
            }

            @Override
            public Boolean visit(ExprConstant x) throws Err {
                if (!(strippedB instanceof ExprConstant)) return false;
                ExprConstant y = (ExprConstant) strippedB;
                return x.op == y.op
                        && (x.op != ExprConstant.Op.NUMBER || x.num == y.num)
                        && (x.op != ExprConstant.Op.STRING || x.string.equals(y.string));
            }

            @Override
            public Boolean visit(ExprITE x) throws Err {
                if (!(strippedB instanceof ExprITE)) return false;
                ExprITE y = (ExprITE) strippedB;
                return areExprsEqual(x.cond, y.cond)
                        && areExprsEqual(x.left, y.left)
                        && areExprsEqual(x.right, y.right);
            }

            @Override
            public Boolean visit(ExprLet x) throws Err {
                if (!(strippedB instanceof ExprLet)) return false;
                ExprLet y = (ExprLet) strippedB;

                // Syntactic equality only
                return areExprsEqual(x.var, y.var)
                        && areExprsEqual(x.expr, y.expr)
                        && areExprsEqual(x.sub, y.sub);
            }

            @Override
            public Boolean visit(ExprQt x) throws Err {
                if (!(strippedB instanceof ExprQt)) return false;
                ExprQt y = (ExprQt) strippedB;
                return x.op == y.op
                        && areDeclListsEqual(x.decls, y.decls)
                        && areExprsEqual(x.sub, y.sub);
            }

            @Override
            public Boolean visit(ExprUnary x) throws Err {
                if (!(strippedB instanceof ExprUnary)) return false;
                ExprUnary y = (ExprUnary) strippedB;
                return x.op == y.op && areExprsEqual(x.sub, y.sub);
            }

            @Override
            public Boolean visit(ExprVar x) throws Err {
                if (!(strippedB instanceof ExprVar)) return false;
                ExprVar y = (ExprVar) strippedB;

                // If using contexts and we can dereference one, we must be able to dereference both
                // and they must be equal.
                if (contextA != null && (contextA.hasTermMapping(x.label) || contextB.hasTermMapping(y.label))) {
                    // We must be able to dereference both.
                    if (!(contextA.hasTermMapping(x.label) && contextB.hasTermMapping(y.label))) {
                        return false;
                    }
                    // And they must compare equal.
                    AnnotatedTerm dereferencedX = contextA.getTermMapping(x.label);
                    AnnotatedTerm dereferencedY = contextB.getTermMapping(y.label);
                    return Objects.equals(dereferencedX, dereferencedY);
                }

                // Otherwise, just compare for syntactic equality.
                return x.label.equals(y.label);
            }

            @Override
            public Boolean visit(Sig x) throws Err {
                if (!(strippedB instanceof Sig)) return false;
                Sig y = (Sig) strippedB;

                // Assume that sigs have unique labels, don't bother checking other fields
                return x.label.equals(y.label);
            }

            @Override
            public Boolean visit(Sig.Field x) throws Err {
                if (!(strippedB instanceof Sig.Field)) return false;
                Sig.Field y = (Sig.Field) strippedB;

                // Don't bother checking the expr - fields should be uniquely named per sig
                return x.label.equals(y.label) && areExprsEqual(x.sig, y.sig);
            }

            @Override
            public Boolean visit(Func x) throws Err {
                if (!(strippedB instanceof Func)) return false;
                Func y = (Func) strippedB;
                return x.isPred == y.isPred && x.label.equals(y.label)
                        && areExprsEqual(x.returnDecl, y.returnDecl)
                        && areDeclListsEqual(x.decls, y.decls);
            }

            @Override
            public Boolean visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot check equality of Assert!");
            }

            @Override
            public Boolean visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot check equality of Macro!");
            }
        }.visitThis(strippedA);
    }

    /**
     * A hashCode() implementation for Expr which is compliant with areExprsEqual() above.
     * That is, two exprs that compare equal via areExprsEqual() have the same hash code.
     */
    public static int exprHashCode(Expr expr) {
        return exprHashCode(expr, null);
    }

    /**
     * A hashCode() implementation for Expr which is compliant with areExprsEqual() above.
     * That is, two exprs that compare equal via areExprsEqual() have the same hash code.
     * If the context passed is not null, this includes the context logic above.
     */
    public static int exprHashCode(Expr expr, VarMappingContext context) {
        if (expr == null) {
            return 3; // arbitrary to avoid NPEs
        }

        expr = PortusUtil.stripPortusNoops(expr);

        // Strategy: hash together the constituents used for the comparison together with
        // a distinct prime for each AST node.
        return new FortressVisitReturn<Integer>() {
            private int hashDecl(Decl decl) {
                return Objects.hash(53, exprHashCode(decl.expr), decl.names.stream()
                        .map(PortusUtil::exprHashCode)
                        .collect(Collectors.toList())
                        .hashCode());
            }

            private int hashDeclList(List<Decl> decls) {
                return Objects.hash(19, decls.stream()
                        .map(this::hashDecl)
                        .collect(Collectors.toList())
                        .hashCode());
            }

            private int hashExprList(List<Expr> expr) {
                return Objects.hash(87, expr.stream()
                        .map(PortusUtil::exprHashCode)
                        .collect(Collectors.toList())
                        .hashCode());
            }

            @Override
            public Integer visit(ExprElementOf x) throws Err {
                return Objects.hash(17, x.tuple.hashCode(), exprHashCode(x.sub));
            }

            @Override
            public Integer visit(ExprBinary x) throws Err {
                return Objects.hash(37, x.op, exprHashCode(x.left), exprHashCode(x.right));
            }

            @Override
            public Integer visit(ExprList x) throws Err {
                return Objects.hash(7, x.op, hashExprList(x.args));
            }

            @Override
            public Integer visit(ExprCall x) throws Err {
                return Objects.hash(23, exprHashCode(x.fun), hashExprList(x.args));
            }

            @Override
            public Integer visit(ExprConstant x) throws Err {
                return Objects.hash(11, x.op,
                        x.op == ExprConstant.Op.NUMBER ? x.num : 0,
                        x.op == ExprConstant.Op.STRING ? x.string : "");
            }

            @Override
            public Integer visit(ExprITE x) throws Err {
                return Objects.hash(61, exprHashCode(x.cond), exprHashCode(x.left), exprHashCode(x.right));
            }

            @Override
            public Integer visit(ExprLet x) throws Err {
                return Objects.hash(43, exprHashCode(x.var), exprHashCode(x.expr), exprHashCode(x.sub));
            }

            @Override
            public Integer visit(ExprQt x) throws Err {
                return Objects.hash(47, x.op, hashDeclList(x.decls), exprHashCode(x.sub));
            }

            @Override
            public Integer visit(ExprUnary x) throws Err {
                return Objects.hash(71, x.op, exprHashCode(x.sub));
            }

            @Override
            public Integer visit(ExprVar x) throws Err {
                if (context != null && context.hasTermMapping(x.label)) {
                    // Use the term mapping instead
                    return Objects.hash(73, context.getTermMapping(x.label));
                }
                return Objects.hash(83, x.label);
            }

            @Override
            public Integer visit(Sig x) throws Err {
                return Objects.hash(91, x.label);
            }

            @Override
            public Integer visit(Sig.Field x) throws Err {
                return Objects.hash(97, x.label, exprHashCode(x.sig));
            }

            @Override
            public Integer visit(Func x) throws Err {
                return Objects.hash(101, x.isPred, x.label, hashDeclList(x.decls), exprHashCode(x.returnDecl));
            }

            @Override
            public Integer visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot compute hash code for Assert!");
            }

            @Override
            public Integer visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot compute hash code for Macro!");
            }
        }.visitThis(expr);
    }

    /** Naively count the symbols that appear in the axioms of a theory. */
    public static int countSymbols(Theory theory) {
        return new CountSymbolsVisitor().countAxiomSymbols(theory);
    }

    /** A visitor which naively counts the symbols in a term/theory. */
    private static class CountSymbolsVisitor implements TermVisitor<Integer> {

        public int countAxiomSymbols(Theory theory) {
            return sumVisits(theory.axioms())
                    + sumVisits(theory.functionDefinitions().map(FunctionDefinition::body))
                    + sumVisits(theory.constantDefinitions().map(ConstantDefinition::body));
        }

        @Override
        public Integer visitTop() {
            return 1;
        }

        @Override
        public Integer visitBottom() {
            return 1;
        }

        @Override
        public Integer visitVar(Var term) {
            return 1;
        }

        @Override
        public Integer visitEnumValue(EnumValue term) {
            return 1;
        }

        @Override
        public Integer visitDomainElement(DomainElement term) {
            return 1;
        }

        @Override
        public Integer visitNot(Not term) {
            return 1 + visit(term.body());
        }

        @Override
        public Integer visitAndList(AndList term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitOrList(OrList term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitDistinct(Distinct term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitImplication(Implication term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitIff(Iff term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitEq(Eq term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitApp(App term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitBuiltinApp(BuiltinApp term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitExists(Exists term) {
            return visitQuantifier(term);
        }

        @Override
        public Integer visitForall(Forall term) {
            return visitQuantifier(term);
        }

        private Integer visitQuantifier(Quantifier term) {
            return 1 + term.vars().size() + visit(term.body());
        }

        @Override
        public Integer visitIntegerLiteral(IntegerLiteral term) {
            return 1;
        }

        @Override
        public Integer visitBitVectorLiteral(BitVectorLiteral term) {
            return 1;
        }

        @Override
        public Integer visitIfThenElse(IfThenElse term) {
            return 1 + visit(term.condition()) + visit(term.ifTrue()) + visit(term.ifFalse());
        }

        @Override
        public Integer visitClosure(Closure term) {
            return 1 + sumVisits(term.allArguments());
        }

        @Override
        public Integer visitReflexiveClosure(ReflexiveClosure term) {
            return 1 + sumVisits(term.allArguments());
        }

        private int sumVisits(scala.collection.Iterable<? extends Term> iterable) {
            // the functional method produced unchecked warnings due to Scala/Java generics interop issues
            final int[] total = {0}; // array is a hack to get around Java lambda 'final' requirements
            iterable.foreach(term -> total[0] += visit(term));
            return total[0];
        }

    }
}
