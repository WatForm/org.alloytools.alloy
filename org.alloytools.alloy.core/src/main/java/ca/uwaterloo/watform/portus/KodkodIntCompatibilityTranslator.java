package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * A translator that tweaks Portus's integer semantics to be the same as that of Kodkod.
 * Specifically, we patch division-by-zero semantics for consistency with Kodkod.
 * The implementation is quite inefficient, so this should not be enabled by default.
 */
final class KodkodIntCompatibilityTranslator extends AbstractTranslator {

    private final SortPolicy sortPolicy;

    public KodkodIntCompatibilityTranslator(Translator topLevel, SortPolicy sortPolicy) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
    }

    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.DIV && expr.op != ExprBinary.Op.REM) return null;

        sortPolicy.checkIsInt(
                expr.op + " requires both sides to be integer expressions!", expr.left, expr.right);

        Term left = recursivelyTranslate(expr.left, context);
        Term right = recursivelyTranslate(expr.right, context);
        if (expr.op == ExprBinary.Op.DIV) {
            return makeKodkodCompatibleDiv(left, right);
        } else { // ExprBinary.Op.REM
            return makeKodkodCompatibleRem(left, right);
        }
    }

    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.DIV && expr.op != ExprBinary.Op.REM) return null;

        if (tuple.size() != 1) {
            throw new ErrorFatal("The arity of an arithmetic operation must be 1.");
        }
        if (!tuple.getSort(0).equals(Sort.Int())) {
            // Fortress will reject = with mismatched sorts, but we know they aren't equal if it's not an int
            return Term.mkBottom();
        }

        Term left = recursivelyTranslate(expr.left, context);
        Term right = recursivelyTranslate(expr.right, context);
        Term operation;
        if (expr.op == ExprBinary.Op.DIV) {
            operation = makeKodkodCompatibleDiv(left, right);
        } else { // ExprBinary.Op.REM
            operation = makeKodkodCompatibleRem(left, right);
        }
        return Term.mkEq(tuple.getTerm(0), operation);
    }

    private Term makeKodkodCompatibleDiv(Term num, Term denom) {
        // Kodkod division-by-zero semantics, as determined empirically:
        //         { -1 if x > 0
        //   x/0 = {  0 if x = 0
        //         {  1 if x < 0
        // Fortress might produce different results, so explicitly implement the above for full
        // compatibility with Kodkod. This is very inefficient but provides compatibility.
        return Term.mkIfThenElse(Term.mkEq(denom, IntegerLiteral.apply(0)),
                Term.mkIfThenElse(Term.mkEq(num, IntegerLiteral.apply(0)),
                        IntegerLiteral.apply(0),
                        Term.mkIfThenElse(Term.mkGT(num, IntegerLiteral.apply(0)),
                                IntegerLiteral.apply(-1),
                                IntegerLiteral.apply(1))),
                Term.mkDiv(num, denom));
    }

    private Term makeKodkodCompatibleRem(Term num, Term denom) {
        // Kodkod remainder-by-zero semantics, as determined empirically: x % 0 = x
        // Fortress might produce different results, so explicitly implement this again.
        // Again, this is inefficient but provides compatibility.
        return Term.mkIfThenElse(
                Term.mkEq(denom, IntegerLiteral.apply(0)), num, Term.mkMod(num, denom));
    }

    @Override
    public String name() {
        return "Kodkod Integer Compatibility";
    }

}
