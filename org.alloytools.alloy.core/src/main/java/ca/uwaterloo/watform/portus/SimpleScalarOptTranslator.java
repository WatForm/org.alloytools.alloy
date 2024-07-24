package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.Objects;

/**
 * Simple optimizations when the expressions involved translate to scalars.
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
        Term intExprScalar = translateIntExprAsScalar(expr, context);
        if (intExprScalar != null) {
            return intExprScalar;
        }
        if (expr instanceof ExprBinary) {
            return translateInEquals((ExprBinary) expr, context);
        } else if (expr instanceof ExprElementOf) {
            return translateExprElementOf((ExprElementOf) expr, context);
        }
        return null;
    }

    private Term translateIntExprAsScalar(Expr expr, TranslationContext context) {
        // Use the cast-to-scalar system to translate integer expressions.
        // This allows us to translate some, but not all, complex integer expressions such as x.f when f: A->Int.
        // We can only translate integer expressions that can be cast to scalar.
        // TODO: Avoid recursive translation issues with DefaultScalarCaster.
        Scalar scalar = scalarCaster.castToScalar(expr, context);
        if (scalar == null) {
            return null;
        }
        if (!scalar.isNilary() || !scalar.getSort().equals(Sort.Int())) {
            throw new ErrorFatal("Internal Portus error: Only integer expressions without free variables can be "
                    + "translated with translate()!");
        }

        // Translate as guard => integer else 0; that is, treat empty sets as 0.
        // This is consistent with Kodkod, which sums sets of integers when used as an integer.
        return Term.mkIfThenElse(scalar.getNilaryGuard(), scalar.getNilaryScalar(), IntegerLiteral.apply(0));
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
        if (!Objects.equals(scalar.getSort(), last.getSort())) {
            return Term.mkBottom();
        }

        return Term.mkAnd(scalar.getGuard(args), Term.mkEq(last.getTerm(), scalar.getScalar(args)));
    }

    /**
     * For "in" and "=", if both are (nilary) scalars, just translate [[left = right]] or [[left in right]]
     * as a plain equals.
     * For "in", if left is a (nilary) scalar, translate [[left in right]] as [[left \in right]].
     * TODO: Bring the optimized in/equals from FunctionOptTranslator here!
     */
    private Term translateInEquals(ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.EQUALS && expr.op != ExprBinary.Op.IN) {
            return null;
        }

        // Note: it should be impossible for them to be non-nilary scalars in this context, but just in case.
        Scalar leftScalar = scalarCaster.castToScalar(expr.left, context);
        if (leftScalar == null || !leftScalar.isNilary()) {
            return null;
        }
        Scalar rightScalar = scalarCaster.castToScalar(expr.right, context);
        if (rightScalar == null || !rightScalar.isNilary()) {
            if (expr.op == ExprBinary.Op.IN) {
                // Left is a scalar - translate as [[guardLeft => left \in right]].
                AnnotatedTerm scalarLeft = leftScalar.getNilaryAnnotatedScalar();
                Term guardLeft = leftScalar.getNilaryGuard();
                return Term.mkImp(guardLeft,
                        rootTranslator.translate(ExprElementOf.make(scalarLeft, expr.right), context));
            } else {
                return null;
            }
        }

        // Short-circuit if the sorts aren't the same
        if (!Objects.equals(leftScalar.getSort(), rightScalar.getSort())) {
            return Term.mkBottom();
        }

        Term guardLeft = leftScalar.getNilaryGuard();
        Term guardRight = rightScalar.getNilaryGuard();
        if (expr.op == ExprBinary.Op.EQUALS) {
            // For equals, either (both guards are false, so both exprs are empty) or (both guards are true, so
            // both expressions are nonempty, and the expressions are equal).
            // Express this as guardLeft => guardRight && left = right else !guardRight.
            return Term.mkIfThenElse(guardLeft,
                    Term.mkAnd(guardRight, Term.mkEq(leftScalar.getNilaryScalar(), rightScalar.getNilaryScalar())),
                    Term.mkNot(guardRight));
        } else { // ExprBinary.Op.IN
            // For in, the left guard is allowed to be false (empty is in anything), but if it is true then the
            // right guard must be true and the scalars must be equal.
            // Express this as guardLeft => guardRight && left = right.
            return Term.mkImp(guardLeft,
                    Term.mkAnd(guardRight, Term.mkEq(leftScalar.getNilaryScalar(), rightScalar.getNilaryScalar())));
        }
    }

}
