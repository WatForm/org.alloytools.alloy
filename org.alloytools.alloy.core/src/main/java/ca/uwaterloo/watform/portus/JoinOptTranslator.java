package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.Term;

/**
 * The join optimization from KT 5.1.
 */
// TODO: Use all the varieties of scalars from the function optimization
final class JoinOptTranslator extends AbstractTranslator {

    public JoinOptTranslator(Translator topLevel) {
        super(topLevel);
    }

    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.JOIN) return null;

        // Translate [[(x1,...,xn) \in v . e]] := [[(v,x1,...,xn) \in e]]
        AnnotatedTerm leftVar = castToTerm(expr.left, context);
        if (leftVar != null) {
            TermTuple newTuple = new TermTuple(leftVar).concat(tuple);
            return recursivelyTranslate(ExprElementOf.make(newTuple, expr.right), context);
        }

        // Translate [[(x1,...,xn) \in e . v]] := [[(x1,...,xn,v) \in e]]
        AnnotatedTerm rightVar = castToTerm(expr.right, context);
        if (rightVar != null) {
            TermTuple newTuple = tuple.concat(new TermTuple(rightVar));
            return recursivelyTranslate(ExprElementOf.make(newTuple, expr.left), context);
        }

        return null;
    }

    /** Return an AnnotatedTerm for the expression if one can be determined, or else return null. */
    private AnnotatedTerm castToTerm(Expr expr, TranslationContext context) {
        expr = PortusUtil.stripPortusNoops(expr);
        if (!(expr instanceof ExprVar)) return null;

        ExprVar exprVar = (ExprVar) expr; 
        String varName = exprVar.label;
        if (context.hasTermMapping(varName)) {
            // it maps to a Fortress var: success
            return context.getTermMapping(varName);
        } else if (context.hasLetMapping(varName)) {
            // try and use the let mapping
            TranslationContext.LetContext letContext = context.getLetMapping(varName);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return castToTerm(letContext.getExpr(), context);
            } finally {
                letContext.resetMapping();
            }
        }

        return null;
    }

}
