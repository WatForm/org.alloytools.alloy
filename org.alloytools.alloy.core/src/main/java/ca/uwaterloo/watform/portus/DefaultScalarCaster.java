package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.Arrays;
import java.util.List;

/**
 * A scalar caster which casts simple expressions to scalars which don't need any additional state.
 */
final class DefaultScalarCaster implements ScalarCaster {

    // The list of builtin constants that we can treat like scalars.
    // TODO: STRING
    private static final ConstList<ExprConstant.Op> SCALAR_CONSTANTS = ConstList.make(Arrays.asList(
            ExprConstant.Op.TRUE,
            ExprConstant.Op.FALSE,
            ExprConstant.Op.NUMBER,
            ExprConstant.Op.MIN,
            ExprConstant.Op.MAX));

    // The translator to use when we need to translate something while casting to scalar.
    private final Translator translator;

    public DefaultScalarCaster(Translator translator) {
        this.translator = translator;
    }

    @Override
    public Pair<AnnotatedTerm, Term> castToScalar(Expr expr, TranslationContext context) {
        expr = PortusUtil.stripPortusNoops(expr);

        if (expr instanceof ExprConstant) {
            // it could be a scalar constant
            ExprConstant.Op op = ((ExprConstant) expr).op;
            if (SCALAR_CONSTANTS.contains(op)) {
                // Translate it as an integer/boolean expression and just use that
                Term scalar = translator.translate(expr, context);
                assert scalar != null;

                // Determine the Fortress sort: true, false are boolean, rest are integers
                Sort sort = (op == ExprConstant.Op.TRUE || op == ExprConstant.Op.FALSE) ? Sort.Bool() : Sort.Int();

                // no guard on usage needed, and there should be no free variables
                List<AnnotatedVar> freeVars = ConstList.make();
                return new Pair<>(new AnnotatedTerm(scalar, sort, freeVars), Term.mkTop());
            }
        } else if (expr instanceof ExprVar) {
            // it could be a variable
            String varName = ((ExprVar) expr).label;
            if (context.hasTermMapping(varName)) {
                AnnotatedTerm fortressTerm = context.getTermMapping(varName);
                assert fortressTerm != null;
                // no guard on the variable usage is needed
                return new Pair<>(fortressTerm, Term.mkTop());
            }
            // TODO: expand lets
        } else if (expr instanceof Sig) {
            // it could be a one sig
            // subset sigs aren't supported by RangeAssigner, so don't bother since they aren't common
            Sig sig = (Sig) expr;
            if (sig.isOne != null && sig instanceof Sig.PrimSig) {
                // use its first/only domain element as the term
                context.rangeAssigner.addRangeAxiom(sig, translator, context);
                Term domainElement = PortusUtil.getOneSigDomainElement((Sig.PrimSig) sig, context);
                Sort sort = context.sortPolicy.getSort(sig);

                // no guard on the domain element usage is needed, and there should be no free variables
                List<AnnotatedVar> freeVars = ConstList.make();
                return new Pair<>(new AnnotatedTerm(domainElement, sort, freeVars), Term.mkTop());
            }
        }
        return null;
    }

}
