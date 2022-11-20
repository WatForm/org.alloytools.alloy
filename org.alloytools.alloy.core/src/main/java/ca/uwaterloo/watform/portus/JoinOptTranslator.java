package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Term;

/**
 * The join optimization from KT 5.1.
 */
final class JoinOptTranslator extends AbstractTranslator {

    public JoinOptTranslator(Translator topLevel) {
        super(topLevel);
    }

    @Override
    public Term translate(VarTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.JOIN) return null;

        // Translate [[(x1,...,xn) \in v . e]] := [[(v,x1,...,xn) \in e]]
        if (expr.left.deNOP() instanceof ExprVar) {
            ExprVar left = (ExprVar) expr.left.deNOP();
            if (context.hasVarMapping(left.label)) {
                AnnotatedVar leftVar = context.getVarMapping(left.label);
                VarTuple newTuple = new VarTuple(leftVar).concat(tuple);
                return recursivelyTranslate(ExprElementOf.make(newTuple, expr.right), context);
            }
        }

        // Translate [[(x1,...,xn) \in e . v]] := [[(x1,...,xn,v) \in e]]
        if (expr.right.deNOP() instanceof ExprVar) {
            ExprVar right = (ExprVar) expr.right.deNOP();
            if (context.hasVarMapping(right.label)) {
                AnnotatedVar rightVar = context.getVarMapping(right.label);
                VarTuple newTuple = tuple.concat(new VarTuple(rightVar));
                return recursivelyTranslate(ExprElementOf.make(newTuple, expr.left), context);
            }
        }

        return null;
    }

}
