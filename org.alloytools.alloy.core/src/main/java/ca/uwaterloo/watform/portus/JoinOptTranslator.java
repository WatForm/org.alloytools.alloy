package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.ExprBinary;
import fortress.msfol.Term;

/**
 * The join optimization from KT 5.1, generalized for general Fortress scalars and not just vars.
 */
final class JoinOptTranslator extends AbstractTranslator {

    private final ScalarCaster scalarCaster;

    public JoinOptTranslator(Translator topLevel, ScalarCaster scalarCaster) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
    }

    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.JOIN) return null;

        // Translate [[(x1,...,xn) \in v . e]] := guard && [[(v,x1,...,xn) \in e]]
        Pair<AnnotatedTerm, Term> leftScalar = scalarCaster.castToScalar(expr.left, context);
        if (leftScalar != null) {
            AnnotatedTerm leftTerm = leftScalar.a;
            Term leftGuard = leftScalar.b;
            TermTuple newTuple = new TermTuple(leftTerm).concat(tuple);
            return Term.mkAnd(leftGuard, recursivelyTranslate(ExprElementOf.make(newTuple, expr.right), context));
        }

        // Translate [[(x1,...,xn) \in e . v]] := guard && [[(x1,...,xn,v) \in e]]
        Pair<AnnotatedTerm, Term> rightScalar = scalarCaster.castToScalar(expr.right, context);
        if (rightScalar != null) {
            AnnotatedTerm rightTerm = rightScalar.a;
            Term rightGuard = rightScalar.b;
            TermTuple newTuple = tuple.concat(new TermTuple(rightTerm));
            return Term.mkAnd(rightGuard, recursivelyTranslate(ExprElementOf.make(newTuple, expr.left), context));
        }

        return null;
    }

}
