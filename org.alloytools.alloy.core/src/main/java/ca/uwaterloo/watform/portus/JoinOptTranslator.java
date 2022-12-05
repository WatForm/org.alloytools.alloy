package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
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
        AnnotatedVar leftVar = castToVar(expr.left, context);
        if (leftVar != null) {
            VarTuple newTuple = new VarTuple(leftVar).concat(tuple);
            return recursivelyTranslate(ExprElementOf.make(newTuple, expr.right), context);
        }

        // Translate [[(x1,...,xn) \in e . v]] := [[(x1,...,xn,v) \in e]]
        AnnotatedVar rightVar = castToVar(expr.right, context);
        if (rightVar != null) {
            VarTuple newTuple = tuple.concat(new VarTuple(rightVar));
            return recursivelyTranslate(ExprElementOf.make(newTuple, expr.left), context);
        }

        return null;
    }

    /** Return an AnnotatedVar for the expression if one can be determined, or else return null. */
    private AnnotatedVar castToVar(Expr expr, TranslationContext context) {
        expr = PortusUtil.stripPortusNoops(expr);
        if (!(expr instanceof ExprVar)) return null;

        ExprVar exprVar = (ExprVar) expr; 
        String varName = exprVar.label;
        if (context.hasVarMapping(varName)) {
            // it maps to a Fortress var: success
            return context.getVarMapping(varName);
        } else if (context.hasLetMapping(varName)) {
            // try and use the let mapping
            TranslationContext.LetContext letContext = context.getLetMapping(varName);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return castToVar(letContext.getExpr(), context);
            } finally {
                letContext.resetMapping();
            }
        }

        return null;
    }

}
