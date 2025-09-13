package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Simple optimizations when the expressions involved translate to scalars.
 */
final class SimpleScalarOptTranslator implements Translator {

    private final Translator rootTranslator;
    private final ScalarCaster scalarCaster;
    private final NameGenerator nameGenerator;

    public SimpleScalarOptTranslator(
            Translator rootTranslator, ScalarCaster scalarCaster, NameGenerator nameGenerator) {
        this.rootTranslator = rootTranslator;
        this.scalarCaster = scalarCaster;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public String name() {
        return "Simple Scalar Optimization";
    }

    @Override
    public Term translate(Expr expr, TranslationContext context) {
        if (expr instanceof ExprBinary) {
            return translateInEquals((ExprBinary) expr, context);
        } else if (expr instanceof ExprElementOf) {
            return translateExprElementOf((ExprElementOf) expr, context);
        } else if (expr instanceof ExprUnary) {
            return translateQuantifierExpr(((ExprUnary) expr).op, ((ExprUnary) expr).sub, context);
        }
        return null;
    }

    /**
     * For [[(x1,...,xn,y) \in f]], if f is a scalar of arity n, translate to "guard(x1,..,xn) && y = f(x1,...,xn)".
     * That this is possible is the definition of a scalar function (see {@link Scalar}).
     */
    private Term translateExprElementOf(ExprElementOf expr, TranslationContext context) {
        Scalar scalar = scalarCaster.castToScalar(expr.sub, context);
        if (scalar == null) {
            return null;
        }

        // If the arities don't match up, let someone else deal with it
        if (expr.tuple.size() != scalar.getArity() + 1) {
            return null;
        }
        AnnotatedTerm last = expr.tuple.getAnnotatedTerm(expr.tuple.size() - 1);
        TermTuple args = expr.tuple.slice(0, expr.tuple.size() - 1);

        // If the sorts don't match up, short-circuit: can't possibly be equal
        if (!Objects.equals(scalar.getResultSort(), last.getSort())) {
            return Term.mkBottom();
        }

        return Term.mkAnd(scalar.getGuard(args, context), Term.mkEq(last.getTerm(), scalar.getScalar(args, context)));
    }

    private Term translateInEquals(ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.EQUALS && expr.op != ExprBinary.Op.IN) return null;
        if (PortusUtil.isDeclarationFormula(expr)) return null; // let DefaultTranslator handle declaration formulas

        Scalar leftScalar = scalarCaster.castToScalar(expr.left, context);
        if (leftScalar == null) {
            return null;
        }
        if (expr.op == ExprBinary.Op.IN) {
            return translateOptimizedIn(leftScalar, expr.right, context);
        }

        Scalar rightScalar = scalarCaster.castToScalar(expr.right, context);
        if (rightScalar == null) {
            return null;
        }
        return translateOptimizedEquals(leftScalar, rightScalar, context);
    }

    /**
     * If castToScalar(f) = (f, guard_f) of arity n, then translate:
     *   [[f in g]] := forall x1,...xn . guard_f(x1,...,xn) => [[(x1,...,xn,f(x1,...,xn)) \in g]]
     * This will be further optimized if g is also a scalar.
     */
    private Term translateOptimizedIn(Scalar leftScalar, Expr right, TranslationContext context) {
        List<AnnotatedVar> argVars = makeArgVars(leftScalar.getArgSorts());

        try {
            context.addFortressVars(argVars);
            TermTuple tuple = TermTuple.fromVars(argVars);
            TermTuple tupleWithLeft = tuple.concat(new TermTuple(leftScalar.getAnnotatedScalar(tuple, context)));

            Term inRight = rootTranslator.translate(ExprElementOf.make(tupleWithLeft, right), context);
            Term body = Term.mkImp(leftScalar.getGuard(tuple, context), inRight);
            return makeSmartForall(argVars, body);
        } finally {
            context.removeFortressVars(argVars);
        }
    }

    /**
     * If castToScalar(f) = (f, guard_f) and castToScalar(g) = (g, guard_g), both of arity n, then translate:
     *   [[f = g]] := forall x1,...,xn . guard_f(x1,...,xn)
     *     guard_f(x1,...,xn) => (guard_g(x1,..,xn) && f(x1,...,xn) = g(x1,...,xn)) else !guard_g(x1,...,xn)
     */
    private Term translateOptimizedEquals(Scalar left, Scalar right, TranslationContext context) {
        if (!left.hasSameSignature(right)) {
            return null; // let someone else deal with it
        }

        List<AnnotatedVar> argVars = makeArgVars(left.getArgSorts());

        try {
            context.addFortressVars(argVars);
            TermTuple tuple = TermTuple.fromVars(argVars);

            // TODO: if right guard is cheaper than left guard, swap them for a (very) slight optimization
            Term body = Term.mkIfThenElse(left.getGuard(tuple, context),
                    Term.mkAnd(right.getGuard(tuple, context),
                            Term.mkEq(left.getScalar(tuple, context), right.getScalar(tuple, context))),
                    Term.mkNot(right.getGuard(tuple, context)));
            return makeSmartForall(argVars, body);
        } finally {
            context.removeFortressVars(argVars);
        }
    }

    /**
     * Optimize quantifier expressions involving scalars, like "no s" and "some s".
     * These can be reduced to just reasoning about the scalar's guard.
     */
    private Term translateQuantifierExpr(ExprUnary.Op quantifier, Expr expr, TranslationContext context) {
        if (quantifier != ExprUnary.Op.SOME && quantifier != ExprUnary.Op.ONE
            && quantifier != ExprUnary.Op.NO && quantifier != ExprUnary.Op.LONE) {
            return null;
        }

        Scalar scalar = scalarCaster.castToScalar(expr, context);

        // just for nilary scalars for a quick test
        if (scalar == null || !scalar.isNilary()) {
            return null;
        }
        switch (quantifier) {
            case SOME:
            case ONE:
                // guard is true
                return scalar.getNilaryGuard(context);
            case NO:
                // guard is false
                return Term.mkNot(scalar.getNilaryGuard(context));
            case LONE:
                // always true
                return Term.mkTop();
            default:
                return null;
        }
    }

    /** Make a list of annotated variables from a list of sorts. */
    private List<AnnotatedVar> makeArgVars(List<Sort> sorts) {
        List<AnnotatedVar> varList = new ArrayList<>();
        for (int i = 0; i < sorts.size(); i++) {
            varList.add(Term.mkVar(nameGenerator.freshName("x" + i)).of(sorts.get(i)));
        }
        return varList;
    }

    /** Return forall vars. body, handling the case where vars is empty. */
    private Term makeSmartForall(List<AnnotatedVar> vars, Term body) {
        if (vars.isEmpty()) {
            return body;
        }
        return Term.mkForall(vars, body);
    }

}
