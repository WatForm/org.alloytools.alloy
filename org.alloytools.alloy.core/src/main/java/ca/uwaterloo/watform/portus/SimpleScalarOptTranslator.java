package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.Term;

import java.util.Objects;

/**
 * Simple optimizations when the expressions involved translate to scalars.
 * TODO: ITE?
 */
final class SimpleScalarOptTranslator implements Translator {

    private final Translator rootTranslator;
    private final ScalarCaster scalarCaster;

    public SimpleScalarOptTranslator(Translator rootTranslator, ScalarCaster scalarCaster) {
        this.rootTranslator = rootTranslator;
        this.scalarCaster = scalarCaster;
    }

    @Override
    public String name() {
        return "Simple Scalar Optimization";
    }

    @Override
    public Term translate(Expr expr, TranslationContext context) {
        if (expr instanceof ExprBinary) {
            return translateExprBinary((ExprBinary) expr, context);
        } else if (expr instanceof ExprElementOf) {
            return translateVarInScalar((ExprElementOf) expr, context);
        }
        return null;
    }

    /**
     * For [[v \in e]], if e is a scalar, translate to "guard && v = e".
     */
    private Term translateVarInScalar(ExprElementOf expr, TranslationContext context) {
        if (expr.tuple.size() != 1) {
            return null;
        }
        AnnotatedTerm term = expr.tuple.getAnnotatedTerm(0);

        Pair<AnnotatedTerm, Term> scalarData = scalarCaster.castToScalar(expr.sub, context);
        if (scalarData == null) {
            return null;
        }
        AnnotatedTerm scalar = scalarData.a;
        Term guard = scalarData.b;

        if (!Objects.equals(term.getSort(), scalar.getSort())) {
            // short-circuit: can't possibly be equal
            return Term.mkBottom();
        }

        return Term.mkAnd(guard, Term.mkEq(term.getTerm(), scalar.getTerm()));
    }

    /**
     * For "in" and "=", if both are scalars, just translate [[left = right]] or [[left in right]]
     * as a plain equals.
     * For "in", if left is a scalar, translate [[left in right]] as [[left \in right]].
     */
    private Term translateExprBinary(ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.EQUALS && expr.op != ExprBinary.Op.IN) {
            return null;
        }

        Pair<AnnotatedTerm, Term> leftScalarData = scalarCaster.castToScalar(expr.left, context);
        if (leftScalarData == null) {
            return null;
        }
        Pair<AnnotatedTerm, Term> rightScalarData = scalarCaster.castToScalar(expr.right, context);
        if (rightScalarData == null) {
            // Left is a scalar - translate as [[guardLeft => left \in right]].
            AnnotatedTerm scalarLeft = leftScalarData.a;
            Term guardLeft = leftScalarData.b;
            return Term.mkImp(guardLeft,
                    rootTranslator.translate(ExprElementOf.make(scalarLeft, expr.right), context));
        }

        // Short-circuit if the sorts aren't the same
        AnnotatedTerm scalarLeft = leftScalarData.a;
        AnnotatedTerm scalarRight = rightScalarData.a;
        if (!Objects.equals(scalarLeft.getSort(), scalarRight.getSort())) {
            return Term.mkBottom();
        }

        Term guardLeft = leftScalarData.b;
        Term guardRight = rightScalarData.b;
        if (expr.op == ExprBinary.Op.EQUALS) {
            // For equals, either (both guards are false, so both exprs are empty) or (both guards are true, so
            // both expressions are nonempty, and the expressions are equal).
            // Express this as guardLeft => guardRight && left = right else !guardRight.
            return Term.mkIfThenElse(guardLeft,
                    Term.mkAnd(guardRight, Term.mkEq(scalarLeft.getTerm(), scalarRight.getTerm())),
                    Term.mkNot(guardRight));
        } else { // ExprBinary.Op.IN
            // For in, the left guard is allowed to be false (empty is in anything), but if it is true then the
            // right guard must be true and the scalars must be equal.
            // Express this as guardLeft => guardRight && left = right.
            return Term.mkImp(guardLeft,
                    Term.mkAnd(guardRight, Term.mkEq(scalarLeft.getTerm(), scalarRight.getTerm())));
        }
    }

}
