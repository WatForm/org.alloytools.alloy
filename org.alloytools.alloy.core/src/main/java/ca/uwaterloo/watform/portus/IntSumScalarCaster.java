package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.*;
import fortress.data.NameGenerator;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * In order to support some standard library functions which only work due to the (undocumented) Alloy feature where
 * sets of integers used in an integer context are treated as their sum, this scalar caster will cast Int-sorted
 * expressions to their sum as an integer.
 * This is done very naively and slowly, so this should be placed after all other integer-related scalar casters.
 */
final class IntSumScalarCaster implements ScalarCaster {

    private final ScalarCaster rootScalarCaster;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public IntSumScalarCaster(ScalarCaster rootScalarCaster, SortPolicy sortPolicy, NameGenerator nameGenerator) {
        this.rootScalarCaster = rootScalarCaster;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public String name() {
        return "Integer Sum Scalar Caster";
    }

    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        // Make sure we're wrapped in a CAST2INT so we know we require a real integer from context
        if (!(expr instanceof ExprUnary)) return null;
        ExprUnary unary = (ExprUnary) expr;
        if (unary.op != ExprUnary.Op.CAST2INT) return null;

        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (resolvant.isNone()) {
            // empty sets treated as integers - hopefully this is okay in arbitrary context...
            return new Scalar(Sort.Int(), IntegerLiteral.apply(0), Term.mkTop());
        }
        if (resolvant.arity() != 1) {
            // only treat unary expressions as integers
            return null;
        }

        // Alloy in fact only requires that at least one possible type is Int
        // e.g. (1+2+A+B) is treated as 3 in an integer context...
        if (!resolvant.getSortsInColumn(0).contains(Sort.Int())) {
            return null;
        }

        // Translate super naively as "sum x: expr | x"
        Decl x = unary.sub.oneOf(nameGenerator.freshName("intSumVar"));
        Expr sumExpr = x.get().sumOver(x);

        return rootScalarCaster.castToScalar(sumExpr, context);
    }

}
