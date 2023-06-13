package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A translator for the function optimization, based on KT 5.5.
 * For now, we optimize only S1->S2->...->[l]one Sn (and they're partial functions).
 */
final class FunctionOptTranslator extends AbstractTranslator implements ScalarCaster, Evaluator {

    // The list of arrow operators which define (partial) functions using "one".
    private static final ConstList<ExprBinary.Op> FUNCTION_ONE_OPS = ConstList.make(Arrays.asList(
            ExprBinary.Op.ANY_ARROW_ONE,
            ExprBinary.Op.SOME_ARROW_ONE,
            ExprBinary.Op.ONE_ARROW_ONE,
            ExprBinary.Op.LONE_ARROW_ONE));

    // Same, but for "lone".
    private static final ConstList<ExprBinary.Op> FUNCTION_LONE_OPS = ConstList.make(Arrays.asList(
            ExprBinary.Op.ISSEQ_ARROW_LONE,
            ExprBinary.Op.ANY_ARROW_LONE,
            ExprBinary.Op.SOME_ARROW_LONE,
            ExprBinary.Op.ONE_ARROW_LONE,
            ExprBinary.Op.LONE_ARROW_LONE));

    // A POJO collecting information about a field subject to this optimization.
    private static final class FieldFuncInfo {
        // Invariant: argSorts.size() + 1 == arity == sum of boundExpr.type().arity() for each boundExpr in boundExprs
        // Also, we must have at least one arg sort.
        public final String funcName;
        public final List<Sort> argSorts;
        public final Sort resultSort;
        public final List<Expr> boundExprs;

        public final int arity;

        // May be null if there's no domain predicate.
        public final String domainPredName;

        public FieldFuncInfo(String funcName, List<Sort> argSorts, Sort resultSort, List<Expr> boundExprs,
                String domainPredName) {
            this.funcName = funcName;
            this.argSorts = argSorts;
            this.resultSort = resultSort;
            this.boundExprs = boundExprs;
            this.domainPredName = domainPredName;

            // enforce the invariant
            this.arity = boundExprs.stream().mapToInt(expr -> expr.type().arity()).sum();
            if (this.arity != argSorts.size() + 1) {
                throw new ErrorFatal("Internal Portus error: function optimization arities do not match!");
            }
            if (argSorts.isEmpty()) {
                throw new ErrorFatal("Internal Portus error: function optimization field with no arg sorts!");
            }
        }

        public FuncDecl getDecl() {
            return FuncDecl.mkFuncDecl(funcName, argSorts, resultSort);
        }
    }

    // The base scalar caster; use this instead of calling castToScalar directly for generality.
    private final ScalarCaster rootScalarCaster;

    // The base evaluator; use this instead of calling evaluate directly for generality.
    private final Evaluator rootEvaluator;

    private final SortPolicy sortPolicy;

    // Should we optimize "A->lone B" as well as "A->one B"?
    private final boolean optimizeLone;

    private final Map<Sig.Field, FieldFuncInfo> optimizedFieldsInfo = new HashMap<>();

    public FunctionOptTranslator(
            Translator topLevel, ScalarCaster rootScalarCaster, Evaluator rootEvaluator,
            SortPolicy sortPolicy, boolean optimizeLone) {
        super(topLevel);
        this.rootScalarCaster = rootScalarCaster;
        this.rootEvaluator = rootEvaluator;
        this.sortPolicy = sortPolicy;
        this.optimizeLone = optimizeLone;
    }

    /** Translate declarations of fields declared as partial functions. */
    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        Expr bound = productWithRightMultiplicity(field.sig, field.decl().expr);
        Pair<List<Expr>, ExprUnary.Op> funcTypeExprsAndMult = getFunctionTypeExprs(bound);
        if (funcTypeExprsAndMult == null) return null; // not a function, not applicable

        List<Sort> allSorts = sortPolicy.getMinimalExprSorts(field,
                "A field declaration must have definite Portus sorts!", context);
        List<Sort> argSorts = allSorts.subList(0, allSorts.size() - 1);
        Sort resultSort = allSorts.get(allSorts.size() - 1);

        String funcName = context.nameGenerator.freshName(field.label);
        // The optimized type is S1 x ... x S{n-1} -> Sn, where n is the field arity
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(funcName, argSorts, resultSort));

        String domainPredName = null;
        if (optimizeLone && funcTypeExprsAndMult.b == ExprUnary.Op.LONE) {
            // Generate the inDomain predicate
            domainPredName = context.nameGenerator.freshName("inDomain");
            context.addFunctionDeclaration(FuncDecl.mkFuncDecl(domainPredName, argSorts, Sort.Bool()));
        }

        FieldFuncInfo info = new FieldFuncInfo(funcName, argSorts, resultSort, funcTypeExprsAndMult.a, domainPredName);
        context.addAxiom(makeOptimizedFunctionAxiom(info, context));
        optimizedFieldsInfo.put(field, info);

        // The return value doesn't matter for field declarations, it just can't be null
        return Term.mkTop();
    }

    private Term makeOptimizedFunctionAxiom(FieldFuncInfo info, TranslationContext context) {
        // forall x1: sort(e1), ..., x{n-1}: sort(e{n-1}) . [[x1 \in e1]] && ... && [[x{n-1} \in e{n-1}]] =>
        //   [[f(x1,...,x{n-1}) \in en]]
        List<Var> vars = new ArrayList<>();
        List<AnnotatedVar> decls = new ArrayList<>();
        for (int i = 0; i < info.argSorts.size(); i++) {
            Var var = Term.mkVar(context.nameGenerator.freshName("x" + i));
            AnnotatedVar decl = var.of(info.argSorts.get(i));
            vars.add(var);
            decls.add(decl);
        }

        Term domainFormula = makeDomainFormula(TermTuple.fromVars(decls), info, context);

        // Map "this" to the first variable, because it represents the signature's atom
        context.addTermMapping("this", new AnnotatedTerm(decls.get(0)));
        Term consequent;
        try {
            AnnotatedTerm funcApp = new AnnotatedTerm(Term.mkApp(info.funcName, vars), info.resultSort, decls);
            consequent = recursivelyTranslate(ExprElementOf.make(funcApp,
                    info.boundExprs.get(info.boundExprs.size() - 1)), context);
        } finally {
            context.removeMapping("this");
        }

        return Term.mkForall(decls, Term.mkImp(domainFormula, consequent));
    }

    /** Create the proper (right-) arrow. */
    private Expr productWithRightMultiplicity(Expr left, Expr right) {
        // unwrap right from its multiplicity and generate the appropriate arrow
        right = right.deNOP();
        ExprUnary.Op mult = right.mult();

        if (right instanceof ExprUnary) {
            ExprUnary wrappedRight = (ExprUnary) right;
            if (wrappedRight.op == ExprUnary.Op.SETOF
                    || wrappedRight.op == ExprUnary.Op.ONEOF
                    || wrappedRight.op == ExprUnary.Op.LONEOF
                    || wrappedRight.op == ExprUnary.Op.SOMEOF) {
                right = wrappedRight.sub.deNOP();
            }
        }

        switch (mult) {
            case SETOF:
                return left.product(right);
            case ONEOF:
                return left.any_arrow_one(right);
            case LONEOF:
                return left.any_arrow_lone(right);
            case SOMEOF:
                return left.any_arrow_some(right);
            case EXACTLYOF:
                // EXACTLYOF should only appear here if the meta feature is used, which we don't support
                throw new ErrorFatal("Portus doesn't support Alloy's 'meta' feature");
            default:
                // we don't support anything else
                throw new ErrorFatal("Unsupported multiplicity: " + mult);
        }
    }

    /** If expr is a function type e1->...->[l]one en, return ([e1,...,en], [l]one), else return null. */
    private Pair<List<Expr>, ExprUnary.Op> getFunctionTypeExprs(Expr expr) {
        if (!(expr instanceof ExprBinary)) return null;
        ExprBinary binExpr = (ExprBinary) expr.deNOP();
        if (!binExpr.op.isArrow) return null;

        Pair<List<Expr>, ExprUnary.Op> rightExprs = getFunctionTypeExprs(binExpr.right);
        if (rightExprs != null) {
            // there's a correct multiplicity on the rightmost arrow, so it's a function
            List<Expr> exprs = new ArrayList<>();
            exprs.add(binExpr.left);
            exprs.addAll(rightExprs.a);
            return new Pair<>(exprs, rightExprs.b);
        } else if (binExpr.right.type().arity() == 1 && (
                FUNCTION_ONE_OPS.contains(binExpr.op) || (
                        optimizeLone && FUNCTION_LONE_OPS.contains(binExpr.op)))) {
            // this is the rightmost arrow and the last element in the arity has correct multiplicity: it's a function
            ExprUnary.Op mult = FUNCTION_ONE_OPS.contains(binExpr.op) ? ExprUnary.Op.ONE : ExprUnary.Op.LONE;
            return new Pair<>(Arrays.asList(binExpr.left, binExpr.right), mult);
        } else {
            return null; // not a function
        }
    }

    /** Translate "tuple \in field" where field is affected by this optimization. */
    @Override
    public Term translate(TermTuple tuple, Sig.Field field, TranslationContext context) {
        if (!optimizedFieldsInfo.containsKey(field)) return null; // not subject to this optimization

        // [[(x1,..,xn) \in f]] := ((x1,...,x{n-1}) in f's domain) && f(x1,...,x{n-1}) = xn
        FieldFuncInfo info = optimizedFieldsInfo.get(field);
        Term domainFormula = makeDomainFormula(tuple.slice(0, tuple.size() - 1), info, context);
        Term funcFormula = Term.mkEq(
                Term.mkApp(info.funcName, tuple.slice(0, tuple.size() - 1).getTerms()),
                tuple.getTerm(tuple.size() - 1));
        return Term.mkAnd(domainFormula, funcFormula);
    }

    /** Translate optimized in/equals, and integer join expressions (e.g. "x.size"). */
    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        if (expr.op == ExprBinary.Op.JOIN) {
            return translateIntJoin(expr, context);
        }

        if (expr.op != ExprBinary.Op.IN && expr.op != ExprBinary.Op.EQUALS) return null;
        int arity = expr.left.type().arity();
        if (expr.right.type().arity() != arity) return null; // default translator can deal with it

        boolean leftOptimized = expr.left instanceof Sig.Field
                && optimizedFieldsInfo.containsKey((Sig.Field) expr.left);
        boolean rightOptimized = expr.right instanceof Sig.Field
                && optimizedFieldsInfo.containsKey((Sig.Field) expr.right);

        if (expr.op == ExprBinary.Op.IN && leftOptimized) {
            // "in" only requires the left operand to be optimized - if the right is optimized that will follow
            return translateOptimizedIn((Sig.Field) expr.left, expr.right, context);
        } else if (expr.op == ExprBinary.Op.EQUALS && leftOptimized && rightOptimized) {
            // "=" requires both to be optimized
            return translateOptimizedEquals((Sig.Field) expr.left, (Sig.Field) expr.right, context);
        } else {
            return null; // not applicable
        }
    }

    private Term translateOptimizedIn(Sig.Field left, Expr right, TranslationContext context) {
        // We assume all validation is already complete.
        // [[e1 in e2]] := forall x1:S1,...,x{n-1}:S{n-1} . ((x1,...,x{n-1}) in f's domain) =>
        //   [[(x1,...,x{n-1},f(x1,...,x{n-1})) \in e2]] where f is e1's function
        FieldFuncInfo leftInfo = optimizedFieldsInfo.get(left);

        List<AnnotatedVar> vars = makeArgVars(leftInfo, context);
        TermTuple termTuple = TermTuple.fromVars(vars);
        Term domainFormula = makeDomainFormula(termTuple, leftInfo, context);

        Term funcApp = Term.mkApp(leftInfo.funcName, termTuple.getTerms());
        TermTuple varsWithFuncApp = termTuple.concat(new TermTuple(funcApp, leftInfo.resultSort, vars));
        Term inRight = recursivelyTranslate(ExprElementOf.make(varsWithFuncApp, right), context);

        return Term.mkForall(vars, Term.mkImp(domainFormula, inRight));
    }

    private Term translateOptimizedEquals(Sig.Field left, Sig.Field right, TranslationContext context) {
        // Again assume all validation is complete.
        // [[e1 = e2]] := forall x1:S1,...,x{n-1}:S{n-1} .
        //   (((x1,...,x{n-1}) in f's domain) <=> ((x1,...,x{n-1}) in g's domain)) &&
        //   (((x1,...,x{n-1}) in f's domain) => f(x1,...,x{n-1}) = g(x1,...,x{n-1})
        // where f is e1's function and g is e2's function.
        // Unfortunately there doesn't seem to exist an equivalent formula using each atomic formula only once.
        FieldFuncInfo leftInfo = optimizedFieldsInfo.get(left);
        FieldFuncInfo rightInfo = optimizedFieldsInfo.get(right);
        if (!leftInfo.argSorts.equals(rightInfo.argSorts)) {
            // let the default translator deal with it
            return null;
        }

        List<AnnotatedVar> vars = makeArgVars(leftInfo, context);
        TermTuple termTuple = TermTuple.fromVars(vars);

        // TODO: if rightDomainFormula is cheaper than leftDomainFormula, swap them for a slight optimization
        Term leftDomainFormula = makeDomainFormula(termTuple, leftInfo, context);
        Term rightDomainFormula = makeDomainFormula(termTuple, rightInfo, context);
        Term funcsEqual = Term.mkEq(
                Term.mkApp(leftInfo.funcName, termTuple.getTerms()),
                Term.mkApp(rightInfo.funcName, termTuple.getTerms()));
        return Term.mkForall(vars, Term.mkAnd(
                Term.mkIff(leftDomainFormula, rightDomainFormula),
                Term.mkImp(leftDomainFormula, funcsEqual)));
    }

    /** Translate "x.y" as an integer expression. We do this here because we need to use the function for y. */
    private Term translateIntJoin(ExprBinary joinExpr, TranslationContext context) {
        // The common case is that "x.y" is an integer expression if y is a function X->one Int and x is a singleton
        // set. We restrict x to a singleton (i.e. bound variable or one sig) because we don't support treating
        // sets of integers like integers. (Kodkod does support this, it just sums them.)
        // We require y to be optimized as a function. Technically we could have y as a singleton set and
        // x: Int one->Y (among other exotic combinations), but this is less common.
        // Then we map x.y to "x in y's domain => y(x) else 0". Defaulting to 0 is consistent with Kodkod's behaviour
        // (because an empty set sums to 0).
        // Similarly, x.y.z will be mapped to "x in y's domain and y(x) in z's domain => z(y(x)) else 0"
        // TODO: might also have to support fun/next (ExprConstant.NEXT) here
        // Note: this case is not supported by the default translator, so this 'optimization' must be activated
        // for expressions of this form to be successfully translated.
        assert joinExpr.op == ExprBinary.Op.JOIN;

        // Just cast it to a scalar - we implement the necesary casting.
        Pair<AnnotatedTerm, Term> scalarResult = rootScalarCaster.castToScalar(joinExpr, context);
        if (scalarResult == null) {
            throw new ErrorFatal(
                "Using join as an integer expression requires a bound variable or a one sig on the LHS and unary "
                + "function fields in all other positions");
        }
        AnnotatedTerm scalar = scalarResult.a;
        Term guard = scalarResult.b;

        if (scalar.getSort() != Sort.Int()) {
            throw new ErrorFatal("A join used as an expression must be of the integer type");
        }

        return Term.mkIfThenElse(guard, scalar.getTerm(), IntegerLiteral.apply(0));
    }

    /** Try to cast expr to a scalar using the function state we have access to. */
    @Override
    public Pair<AnnotatedTerm, Term> castToScalar(Expr expr, TranslationContext context) {
        expr = PortusUtil.stripPortusNoops(expr);

        if (expr instanceof ExprBinary) {
            ExprBinary binExpr = (ExprBinary) expr;
            if (binExpr.op == ExprBinary.Op.JOIN) {
                // it could be a join expression that resolves to a scalar
                // "x.y" is a scalar if (and maybe only if) x is a scalar and y is optimized as a function
                // then the scalar term is y(x)
                Pair<AnnotatedTerm, Term> leftScalarData = rootScalarCaster.castToScalar(binExpr.left, context);
                if (leftScalarData == null) {
                    return null;
                }
                AnnotatedTerm leftScalar = leftScalarData.a;
                Term leftScalarGuard = leftScalarData.b;

                Expr right = PortusUtil.stripPortusNoops(binExpr.right);
                if (!(right instanceof Sig.Field)) {
                    return null;
                }
                Sig.Field field = (Sig.Field) right;
                if (!optimizedFieldsInfo.containsKey(field)) {
                    return null;
                }
                FieldFuncInfo optInfo = optimizedFieldsInfo.get(field);
                if (optInfo.argSorts.size() != 1) {
                    // we require unary functions
                    // TODO this restriction could be loosened to allow translating into things like f(g(x),h(y))
                    return null;
                }

                Term inDomain = makeDomainFormula(new TermTuple(leftScalar), optInfo, context);
                Term scalar = Term.mkApp(optInfo.funcName, leftScalar.getTerm());
                Term guard = Term.mkAnd(leftScalarGuard, inDomain);
                Sort sort = optInfo.resultSort;

                // There shouldn't be any extra free variables in the scalar
                List<AnnotatedVar> scalarFreeVars = ConstList.make();
                return new Pair<>(new AnnotatedTerm(scalar, sort, scalarFreeVars), guard);
            }
        }
        return null;
    }

    /** Evaluate fields we optimized here. */
    @Override
    public TupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        if (!(expr instanceof Sig.Field)) return null;
        Sig.Field field = (Sig.Field) expr;
        if (!optimizedFieldsInfo.containsKey(field)) return null;

        FieldFuncInfo info = optimizedFieldsInfo.get(field);

        // Find the sets of n-1 atoms for which the domain predicate is true then map to get the final atoms
        TupleSet domain = getTuplesInDomain(info, solution, context);
        return domain.stream()
                .map(args -> SetOps.concatenate(args, solution.evaluateTerm(Term.mkApp(info.funcName, args))))
                .collect(TupleSet.collect(info.arity));
    }

    private List<AnnotatedVar> makeArgVars(FieldFuncInfo info, TranslationContext context) {
        List<AnnotatedVar> varList = new ArrayList<>();
        for (int i = 0; i < info.argSorts.size(); i++) {
            varList.add(Term.mkVar(context.nameGenerator.freshName("x" + i)).of(info.argSorts.get(i)));
        }
        return varList;
    }

    /**
     * Given some variables x1,...,xn and the list of bounds of a field with this optimization
     * (i.e. for sig S { f: e1->e2->one e3 }, the bound expressions are S,e1,e2,e3),
     * return a term expressing "(x1,...,x{n-1}) is in the domain of the function representing the field".
     */
    private Term makeDomainFormula(TermTuple vars, FieldFuncInfo info, TranslationContext context) {
        if (info.domainPredName != null) {
            // use the domain predicate instead (supports lone)
            return Term.mkApp(info.domainPredName, vars.getTerms());
        }

        // Map "this" to the first var in the tuple, because it's the one bounded by the enclosing signature.
        context.addTermMapping("this", vars.getAnnotatedTerm(0));
        try {
            List<Term> conjuncts = new ArrayList<>();
            int varIdx = 0;

            // Ignore the last bound expr, it's for the result
            for (Expr expr : info.boundExprs.subList(0, info.boundExprs.size() - 1)) {
                int arity = expr.type().arity();
                if (varIdx + arity > vars.size()) {
                    // out of variables - arities are mismatched
                    throw new ErrorFatal("Mismatched arities in optimized field expression!");
                }

                TermTuple subTuple = vars.slice(varIdx, varIdx + arity);
                Term conjunct = recursivelyTranslate(ExprElementOf.make(subTuple, expr), context);
                conjuncts.add(conjunct);

                varIdx += arity;
            }

            return conjuncts.isEmpty() ? Term.mkTop() : Term.mkAnd(conjuncts);
        } finally {
            context.removeMapping("this");
        }
    }

    // TODO: test this (significantly!)
    private TupleSet getTuplesInDomain(
            FieldFuncInfo info, FortressSolution solution, TranslationContext context) {
        if (info.domainPredName != null) {
            // reverse the domain predicate if available
            return solution.functionPreimage(info.getDecl(), Term.mkTop());
        }

        // Take the product of all the bound exprs in the domain formula above
        // If there's no "this", just evaluate the exprs
        TupleSet first = null;
        TupleSet result = TupleSet.singleton(Collections.emptyList()); // the identity for cartesian product
        for (Expr expr : info.boundExprs.subList(0, info.boundExprs.size() - 1)) {
            int arity = expr.type().arity();

            // TODO: this is overkill, if this is a bottleneck then just write a search-for-free-var routine
            boolean hasThis = PortusUtil.computeFreeVariables(expr, context, sortPolicy).stream()
                    .anyMatch(var -> var.name().equals("this"));

            TupleSet exprResult;
            if (hasThis) {
                if (first == null) {
                    // first should be the sig and defines this, so it shouldn't contain this
                    throw new ErrorFatal("First bound expr can't contain this!");
                }
                if (first.arity() != 1) {
                    // first should be the sig so it should translate to a pure set (arity 1)
                    throw new ErrorFatal("First bound expr should be a pure set!");
                }

                // Use each value in the sig in turn as "this" and then union the results together
                Sort sigSort = info.argSorts.get(0);
                exprResult = first.singleValueStream().map(thisValue -> {
                    context.addTermMapping("this", new AnnotatedTerm(thisValue, sigSort));
                    try {
                        return rootEvaluator.evaluate(expr, solution, context);
                    } finally {
                        context.removeMapping("this");
                    }
                }).reduce(TupleSet.empty(arity), TupleSet::union);
            } else {
                exprResult = rootEvaluator.evaluate(expr, solution, context);
            }

            if (first == null) {
                first = exprResult;
            }

            // Take the product of the results for each expression
            result = result.cartesianProduct(exprResult);
        }

        return result;
    }

}
