package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.Term;

/**
 * Simple optimizations when the expressions involved translate to scalars.
 */
final class SimpleScalarOptTranslator extends AbstractTranslator {

    private final ScalarCaster scalarCaster;

    public SimpleScalarOptTranslator(Translator topLevel, ScalarCaster scalarCaster) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
    }

    /**
     * For "in" and "=", if both are scalars, just translate [[left = right]] or [[left in right]]
     * as a plain equals.
     */
    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.EQUALS && expr.op != ExprBinary.Op.IN) {
            return null;
        }

        Pair<AnnotatedTerm, Term> leftScalarData = scalarCaster.castToScalar(expr.left, context);
        if (leftScalarData == null) {
            return null;
        }
        Pair<AnnotatedTerm, Term> rightScalarData = scalarCaster.castToScalar(expr.right, context);
        if (rightScalarData == null) {
            return null;
        }

        // Short-circuit if the sorts aren't the same
        AnnotatedTerm scalarLeft = leftScalarData.a;
        AnnotatedTerm scalarRight = rightScalarData.a;
        if (scalarLeft.getSort() != scalarRight.getSort()) {
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
