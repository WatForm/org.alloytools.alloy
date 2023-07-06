package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
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
 *
 * It also acts as a root ScalarCaster similarly, keeping a list of scalar casters
 * and delegating to them to attempt to cast an expression to scalar.
 *
 * Similarly, it also acts as a root Evaluator.
 * TODO: This is getting unsustainable. Also, caching.
 */
final class TranslatorManager implements Translator, ScalarCaster, Evaluator {

    private final List<Translator> translators = new ArrayList<>();
    private final List<ScalarCaster> scalarCasters = new ArrayList<>();
    private final List<Evaluator> evaluators = new ArrayList<>();

    /**
     * Create a TranslatorManager that uses the given reporter and options
     * to create its list of translators to delegate to.
     * @param options Fortress options used to create the list of translators.
     *                This usually means enabling/disabling optimizations based
     *                on the options selected by the user.
     */
    public TranslatorManager(PortusOptions options, SortPolicy sortPolicy) {
        // TODO: use options to come up with a list of translators
        // but for now:
        OneSigOptTranslator oneSigOpt = new OneSigOptTranslator(this, sortPolicy);
        FunctionOptTranslator functionOpt = new FunctionOptTranslator(this, this, this, sortPolicy, true);
        OrderingModuleOptTranslator orderingModuleOpt = new OrderingModuleOptTranslator(this, this, sortPolicy);
        DefaultTranslator defaultTranslator = new DefaultTranslator(
                this, new ConstantsScopeAxiomStrategy(sortPolicy), sortPolicy);
        translators.add(new SimpleScalarOptTranslator(this));
        translators.add(oneSigOpt);
        translators.add(functionOpt);
        translators.add(new JoinOptTranslator(this, this));
        translators.add(orderingModuleOpt);
        translators.add(defaultTranslator);

        scalarCasters.add(oneSigOpt);
        scalarCasters.add(functionOpt);
        scalarCasters.add(orderingModuleOpt);
        scalarCasters.add(new DefaultScalarCaster(this, this, sortPolicy));

        evaluators.add(oneSigOpt);
        evaluators.add(functionOpt);
        evaluators.add(defaultTranslator);
        evaluators.add(new SimpleEvaluator(this));
        evaluators.add(new BruteForceEvaluator(this, sortPolicy));
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

    /**
     * Attempt to cast expr to scalar by delegating to the list of scalar casters.
     * @return (scalar term, guard), as casted by some scalar caster, or null if no caster can cast.
     */
    @Override
    public Pair<AnnotatedTerm, Term> castToScalar(Expr expr, TranslationContext context) {
        for (ScalarCaster scalarCaster : scalarCasters) {
            Pair<AnnotatedTerm, Term> attempt = scalarCaster.castToScalar(expr, context);
            if (attempt != null) {
                return attempt;
            }
        }
        return null;
    }

    /**
     * Evaluate expr under the solution by delegating to the list of evaluators.
     * @return a tuple set corresponding to the expr's evaluation under the solution.
     */
    @Override
    public ValueTupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        for (Evaluator evaluator : evaluators) {
            ValueTupleSet attempt = evaluator.evaluate(expr, solution, context);
            if (attempt != null) {
                return attempt;
            }
        }
        throw new ErrorFatal("Cannot evaluate: " + expr);
    }

}
