package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * The root translator. Immutable.
 * 
 * It is aware of all other translators and uses the FortressOptions to come
 * up with an appropriate order of delegation. For each expression it's asked
 * to translate, it delegates to its list of translators in order until one of
 * them successfully translates the expression. This allows optimizations to
 * translate certain expressions earlier in the list.
 */
// TODO: is there a better name for this? RootTranslator?
final class TranslatorManager implements Translator {

    private final List<Translator> translators = new ArrayList<>();

    /**
     * Create a TranslatorManager that uses the given reporter and options
     * to create its list of translators to delegate to.
     * @param options Fortress options used to create the list of translators.
     *                This usually means enabling/disabling optimizations based
     *                on the options selected by the user.
     */
    public TranslatorManager(FortressOptions options) {
        // TODO: use options to come up with a list of translators
        // but for now:
        translators.add(new FunctionOptTranslator(this, true));
        translators.add(new JoinOptTranslator(this));
        translators.add(new OrderingModuleOptTranslator(this));
        translators.add(new DefaultTranslator(this, new CardinalityScopeAxiomStrategy()));
    }

    /**
     * Translate an expression by delegating to the list of translators.
     * @return The Fortress term for the Alloy expression, as translated by some translator.
     * @throws ErrorFatal If no translator implements a translation for this expression.
     */
    @Override
    public Term translate(Expr expr, TranslationContext context) throws Err {
        for (Translator translator : translators) {
            Term attempt = translator.translate(expr, context);
            if (attempt != null) {
                return attempt;
            }
        }
        throw new ErrorFatal("No Fortress translation implemented for node: " + expr);
    }

}
