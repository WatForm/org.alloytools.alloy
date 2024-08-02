package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * Translate integer expressions by casting them to scalar.
 * This allows us to translate some, but not all, complex integer expressions such as x.f when f: A->Int by relying on
 * the cast-to-scalar system. These integer expressions are otherwise untranslatable.
 * This should be run after all translators that translate integer expressions (even DefaultTranslator) so that every
 * integer expression that can be directly handled is. DefaultScalarCaster relies on the Translator system to cast
 * basic integer expressions to scalar, so putting this translator at the very end avoids stack overflows.
 */
final class IntAsScalarTranslator implements Translator {

    private final ScalarCaster scalarCaster;

    public IntAsScalarTranslator(ScalarCaster scalarCaster) {
        this.scalarCaster = scalarCaster;
    }

    @Override
    public Term translate(Expr expr, TranslationContext context) {
        Scalar scalar = scalarCaster.castToScalar(expr, context);
        if (scalar == null) {
            return null;
        }
        if (!scalar.isNilary() || !scalar.getResultSort().equals(Sort.Int())) {
            throw new ErrorFatal("Internal Portus error: Only formulas and integer expressions without free variables "
                    + "can be translated with translate()!");
        }

        // Translate as guard => integer else 0; that is, treat empty sets as 0.
        // This is consistent with Kodkod, which sums sets of integers when used as an integer.
        return Term.mkIfThenElse(scalar.getNilaryGuard(), scalar.getNilaryScalar(), IntegerLiteral.apply(0));
    }

    @Override
    public String name() {
        return "Integers As Scalars Translator";
    }

}
