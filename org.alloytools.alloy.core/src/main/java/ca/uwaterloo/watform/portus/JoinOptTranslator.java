package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.Term;

/**
 * The join optimization from KT 5.1, generalized for general Fortress scalars.
 * Also includes the composition scalar caster.
 */
final class JoinOptTranslator extends AbstractTranslator implements ScalarCaster {

    private final ScalarCaster scalarCaster;

    public JoinOptTranslator(Translator topLevel, ScalarCaster scalarCaster) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
    }

    @Override
    public String name() {
        return "Join Optimization";
    }

    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.JOIN) return null;

        // Translate [[(x1,...,xn) \in f.e]] := guard(x1,...,xm) && [[(f(x1,...,xm),x{m+1},...,xn) \in e]]
        // when f is a scalar function of arity m<=n. Note m>n is impossible since the arities don't work out.
        Scalar leftScalar = scalarCaster.castToScalar(expr.left, context);
        if (leftScalar != null) {
            TermTuple scalarArgs = tuple.slice(0, leftScalar.getArity());
            AnnotatedTerm scalarCall = leftScalar.getAnnotatedScalar(scalarArgs, context);
            Term scalarGuard = leftScalar.getGuard(scalarArgs, context);
            TermTuple newTuple = new TermTuple(scalarCall).concat(tuple.slice(leftScalar.getArity(), tuple.size()));
            return Term.mkAnd(scalarGuard, recursivelyTranslate(ExprElementOf.make(newTuple, expr.right), context));
        }

        // Translate [[(x1,...,xn) \in e.v]] := guard && [[(x1,...,xn,v) \in e]] when v is a nilary scalar (of arity 0).
        // This is the best we can do since functions have their outputs on the right.
        Scalar rightScalar = scalarCaster.castToScalar(expr.right, context);
        if (rightScalar != null && rightScalar.isNilary()) {
            AnnotatedTerm rightTerm = rightScalar.getNilaryAnnotatedScalar(context);
            Term rightGuard = rightScalar.getNilaryGuard(context);
            TermTuple newTuple = tuple.concat(new TermTuple(rightTerm));
            return Term.mkAnd(rightGuard, recursivelyTranslate(ExprElementOf.make(newTuple, expr.left), context));
        }

        return null;
    }

    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        if (!(expr instanceof ExprBinary)) return null;
        ExprBinary join = (ExprBinary) expr;
        if (join.op != ExprBinary.Op.JOIN) return null;

        Scalar composition = castComposeJoin(join.left, join.right, context);
        if (composition != null) {
            return composition;
        }

        // Attempt castToScalar(s.t) := castToScalar(t.~s) if s has arity 2 and t has arity 1.
        // This helps on the off-chance that ~s is a unary scalar function and t is a nilary scalar.
        if (join.left.type().arity() == 2 && join.right.type().arity() == 1) {
            return scalarCaster.castToScalar(join.right.join(join.left.transpose()), context);
        }

        return null;
    }

    public Scalar castComposeJoin(Expr left, Expr right, TranslationContext context) {
        // If castToScalar(f) = (f1, g1) of arity n and castToScalar(g) = (f2, g2) of arity m>=1, then
        // castToScalar(f.g) = (f', g') of arity n+m-1, where:
        //   f'(x1,...,xn,y2,...,ym) = f2(f1(x1,...,xn),y2,...,ym)
        //   g'(x1,...,xn,y2,...,ym) = g1(x1,...,xn) && g2(f1(x1,...,xn),y2,...,ym)

        Scalar leftScalar = scalarCaster.castToScalar(left, context);
        if (leftScalar == null) return null;

        Scalar rightScalar = scalarCaster.castToScalar(right, context);
        if (rightScalar == null || rightScalar.isNilary()) return null;

        return Scalar.compose(leftScalar, rightScalar, context.getVarMappingContext());
    }

}
