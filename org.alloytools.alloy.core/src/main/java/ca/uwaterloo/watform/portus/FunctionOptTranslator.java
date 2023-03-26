package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A translator for the function optimization, based on KT 5.5.
 * For now, we optimize only S1->S2->...->[l]one Sn (and they're partial functions).
 */
final class FunctionOptTranslator extends AbstractTranslator {

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
        // Invariant: argSorts.size() + 1 == sum of boundExpr.type().arity() for each boundExpr in boundExprs
        // Also, we must have at least one arg sort.
        public final String funcName;
        public final List<Sort> argSorts;
        public final Sort resultSort;
        public final List<Expr> boundExprs;

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
            int totalArity = boundExprs.stream().mapToInt(expr -> expr.type().arity()).sum();
            if (totalArity != argSorts.size() + 1) {
                throw new ErrorFatal("Internal Portus error: function optimization arities do not match!");
            }
            if (argSorts.isEmpty()) {
                throw new ErrorFatal("Internal Portus error: function optimization field with no arg sorts!");
            }
        }
    }

    // Should we optimize "A->lone B" as well as "A->one B"?
    private final boolean optimizeLone;

    private final Map<Sig.Field, FieldFuncInfo> optimizedFieldsInfo = new HashMap<>();

    public FunctionOptTranslator(Translator topLevel, boolean optimizeLone) {
        super(topLevel);
        this.optimizeLone = optimizeLone;
    }

    /** Translate declarations of fields declared as partial functions. */
    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        Expr bound = productWithRightMultiplicity(field.sig, field.decl().expr);
        Pair<List<Expr>, ExprUnary.Op> funcTypeExprsAndMult = getFunctionTypeExprs(bound);
        if (funcTypeExprsAndMult == null) return null; // not a function, not applicable

        List<Sort> allSorts = context.sortPolicy.getMinimalExprSorts(field,
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
        //   [[y \in en]][f(x1,...,x{n-1})/y]
        List<Var> vars = new ArrayList<>();
        List<AnnotatedVar> decls = new ArrayList<>();
        for (int i = 0; i < info.argSorts.size(); i++) {
            Var var = Term.mkVar(context.nameGenerator.freshName("x" + i));
            AnnotatedVar decl = var.of(info.argSorts.get(i));
            vars.add(var);
            decls.add(decl);
        }

        Term domainFormula = makeDomainFormula(new VarTuple(decls), info, context);

        Term consequent;
        try {
            // Map "this" to the first variable, because it represents the signature's atom
            context.addVarMapping("this", decls.get(0));

            // do this substitution because ExprElementOf/VarTuple only supports AnnotatedVars
            AnnotatedVar y = Term.mkVar(context.nameGenerator.freshName("y")).of(info.resultSort);
            Term funcApp = Term.mkApp(info.funcName, vars);
            consequent = recursivelyTranslate(
                    ExprElementOf.make(y, info.boundExprs.get(info.boundExprs.size() - 1)), context);
            consequent = PortusUtil.substitute(y, funcApp, consequent);
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
    public Term translate(VarTuple tuple, Sig.Field field, TranslationContext context) {
        if (!optimizedFieldsInfo.containsKey(field)) return null; // not subject to this optimization

        // [[(x1,..,xn) \in f]] := ((x1,...,x{n-1}) in f's domain) && f(x1,...,x{n-1}) = xn
        FieldFuncInfo info = optimizedFieldsInfo.get(field);
        Term domainFormula = makeDomainFormula(tuple.slice(0, tuple.size() - 1), info, context);
        Term funcFormula = Term.mkEq(
                Term.mkApp(info.funcName, tuple.slice(0, tuple.size() - 1).getVars()),
                tuple.getVar(tuple.size() - 1));
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
        //   [[(x1,...,x{n-1},y) \in e2]][f(x1,...,x{n-1})/y] where f is e1's function
        FieldFuncInfo leftInfo = optimizedFieldsInfo.get(left);

        VarTuple vars = makeArgVars(leftInfo, context);
        Term domainFormula = makeDomainFormula(vars, leftInfo, context);

        // do this substitution because VarTuple only supports vars
        AnnotatedVar y = Term.mkVar(context.nameGenerator.freshName("y")).of(leftInfo.resultSort);
        Term funcApp = Term.mkApp(leftInfo.funcName, vars.getVars());
        VarTuple varsWithY = vars.concat(new VarTuple(y));
        Term inRight = recursivelyTranslate(ExprElementOf.make(varsWithY, right), context);
        inRight = PortusUtil.substitute(y, funcApp, inRight);

        return Term.mkForall(vars.getAnnotatedVars(), Term.mkImp(domainFormula, inRight));
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

        VarTuple vars = makeArgVars(leftInfo, context);

        // TODO: if rightDomainFormula is cheaper than leftDomainFormula, swap them for a slight optimization
        Term leftDomainFormula = makeDomainFormula(vars, leftInfo, context);
        Term rightDomainFormula = makeDomainFormula(vars, rightInfo, context);
        Term funcsEqual = Term.mkEq(
                Term.mkApp(leftInfo.funcName, vars.getVars()),
                Term.mkApp(rightInfo.funcName, vars.getVars()));
        return Term.mkForall(vars.getAnnotatedVars(), Term.mkAnd(
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

        // Offload all the work to castToScalar because it's recursive.
        Pair<Term, Pair<Term, Sort>> scalarResult = castToScalar(joinExpr, context);
        Term scalar = scalarResult.a;
        Term guard = scalarResult.b.a;
        Sort sort = scalarResult.b.b;

        if (sort != Sort.Int()) {
            throw new ErrorFatal("A join used as an expression must be of the integer type");
        }

        return Term.mkIfThenElse(guard, scalar, IntegerLiteral.apply(0));
    }

    /**
     * Return a pair of a variable or domain element and a pair of a guard and its sort corresponding to the expression,
     * or throw an exception if expr is not (definitely) a scalar.
     * Use of the scalar term must be conditioned on the guard (it could be e.g. a domain check).
     * The guard will be Top if it is not necessary.
     */
    private Pair<Term, Pair<Term, Sort>> castToScalar(Expr expr, TranslationContext context) {
        expr = expr.deNOP();

        if (expr instanceof ExprVar) {
            // it could be a variable
            String varName = ((ExprVar) expr).label;
            if (context.hasVarMapping(varName)) {
                AnnotatedVar fortressVar = context.getVarMapping(varName);
                assert fortressVar != null;
                // no guard on the variable usage is needed
                return new Pair<>(fortressVar.variable(), new Pair<>(Term.mkTop(), fortressVar.sort()));
            }
        } else if (expr instanceof Sig) {
            // it could be a one sig
            Sig sig = (Sig) expr;
            if (sig.isOne != null) {
                // use its first/only domain element as the term
                Term domainElement = PortusUtil.getOneSigDomainElement(sig, context);
                // no guard on the domain element usage is needed
                return new Pair<>(domainElement, new Pair<>(Term.mkTop(), context.sortPolicy.getSort(sig)));
            }
        } else if (expr instanceof ExprBinary) {
            ExprBinary binExpr = (ExprBinary) expr;
            if (binExpr.op == ExprBinary.Op.JOIN) {
                // it could be a join expression that resolves to a scalar
                // "x.y" is a scalar if (and maybe only if) x is a scalar and y is optimized as a function
                // then the scalar term is y(x)
                Pair<Term, Pair<Term, Sort>> leftScalarData = castToScalar(binExpr.left, context);
                Term leftScalar = leftScalarData.a;
                Term leftScalarGuard = leftScalarData.b.a;
                Sort leftScalarSort = leftScalarData.b.b;

                Expr right = binExpr.right.deNOP();
                if (!(right instanceof Sig.Field)) {
                    throw new ErrorFatal(
                            "All join operands except the first in an integer join expression must be pure fields");
                }
                Sig.Field field = (Sig.Field) right;
                if (!optimizedFieldsInfo.containsKey(field)) {
                    throw new ErrorFatal(
                            "All join operands except the first in an integer join expression must be functions");
                }
                FieldFuncInfo optInfo = optimizedFieldsInfo.get(field);
                if (optInfo.argSorts.size() != 1) {
                    // this restriction could probably be loosened to allow translating into things like f(g(x),h(y))
                    throw new ErrorFatal("Functions in an integer join expression must be unary");
                }

                // We want to express "leftScalar in domain of field", but leftScalar could be an arbitrary Term while
                // makeDomainFormula requires a VarTuple (so AnnotatedVars). To get around this, use a temporary
                // variable and substitute it with the term.
                AnnotatedVar tempVar = Term.mkVar(context.nameGenerator.freshName("temp")).of(leftScalarSort);
                Term unsubbedInDomain = makeDomainFormula(new VarTuple(tempVar), optInfo, context);
                Term inDomain = PortusUtil.substitute(tempVar, leftScalar, unsubbedInDomain);

                Term scalar = Term.mkApp(optInfo.funcName, leftScalar);
                Term guard = Term.mkAnd(leftScalarGuard, inDomain);
                Sort sort = optInfo.resultSort;
                return new Pair<>(scalar, new Pair<>(guard, sort));
            }
        }
        throw new ErrorFatal("Using join as an integer expression requires a bound variable or one sig on the LHS");
    }

    private VarTuple makeArgVars(FieldFuncInfo info, TranslationContext context) {
        List<AnnotatedVar> varList = new ArrayList<>();
        for (int i = 0; i < info.argSorts.size(); i++) {
            varList.add(Term.mkVar(context.nameGenerator.freshName("x" + i)).of(info.argSorts.get(i)));
        }
        return new VarTuple(varList);
    }

    /**
     * Given some variables x1,...,xn and the list of bounds of a field with this optimization
     * (i.e. for sig S { f: e1->e2->one e3 }, the bound expressions are S,e1,e2,e3),
     * return a term expressing "(x1,...,x{n-1}) is in the domain of the function representing the field".
     */
    private Term makeDomainFormula(VarTuple vars, FieldFuncInfo info, TranslationContext context) {
        if (info.domainPredName != null) {
            // use the domain predicate instead (supports lone)
            return Term.mkApp(info.domainPredName, vars.getVars());
        }

        // Map "this" to the first var in the tuple, because it's the one bounded by the enclosing signature.
        try {
            context.addVarMapping("this", vars.getAnnotatedVar(0));

            List<Term> conjuncts = new ArrayList<>();
            int varIdx = 0;

            // Ignore the last bound expr, it's for the result
            for (Expr expr : info.boundExprs.subList(0, info.boundExprs.size() - 1)) {
                int arity = expr.type().arity();
                if (varIdx + arity > vars.size()) {
                    // out of variables - arities are mismatched
                    throw new ErrorFatal("Mismatched arities in optimized field expression!");
                }

                VarTuple subTuple = vars.slice(varIdx, varIdx + arity);
                Term conjunct = recursivelyTranslate(ExprElementOf.make(subTuple, expr), context);
                conjuncts.add(conjunct);

                varIdx += arity;
            }

            return conjuncts.isEmpty() ? Term.mkTop() : Term.mkAnd(conjuncts);
        } finally {
            context.removeMapping("this");
        }
    }

}
