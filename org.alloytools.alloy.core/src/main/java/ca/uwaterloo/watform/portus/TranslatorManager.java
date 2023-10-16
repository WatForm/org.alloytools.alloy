package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
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
 * 
 * It is also responsible for coming up with a list of all Passes and running
 * the entire translation by iterating through the passes.
 *
 * TODO: Caching!
 */
final class TranslatorManager implements Translator, ScalarCaster, Evaluator {

    private final PortusStatistics statistics;

    private final List<Pass> passes = new ArrayList<>();

    private final List<Translator> translators = new ArrayList<>();
    private final List<ScalarCaster> scalarCasters = new ArrayList<>();
    private final List<Evaluator> evaluators = new ArrayList<>();

    private final boolean useCaching;
    private final ContextExprCache<Term> translationCache;
    private final ContextExprCache<Pair<AnnotatedTerm, Term>> castToScalarCache;

    /**
     * Create a TranslatorManager that uses the given reporter and options
     * to create its list of translators to delegate to.
     * @param options Fortress options used to create the list of translators.
     *                This usually means enabling/disabling optimizations based
     *                on the options selected by the user.
     */
    public TranslatorManager(PortusOptions options, PortusStatistics statistics, SortPolicy sortPolicy) {
        this.statistics = statistics;

        this.useCaching = options.enableCaching;
        this.translationCache = new ContextExprCache<>(sortPolicy);
        this.castToScalarCache = new ContextExprCache<>(sortPolicy);

        // Use the options to come up with a list of translators
        ScopeAxiomStrategy scopeAxiomStrategy;
        if (options.enableConstantsScopeAxiomStrategy) {
            scopeAxiomStrategy = new ConstantsScopeAxiomStrategy(sortPolicy);
        } else {
            scopeAxiomStrategy = new CardinalityScopeAxiomStrategy(sortPolicy);
        }
        SigAxioms sigAxioms = new SigAxioms(this, sortPolicy);

        // There *shouldn't* be side effects in the constructors, so it should be ok to always construct these
        OneSigOptTranslator oneSigOpt = new OneSigOptTranslator(this, sortPolicy, sigAxioms);
        FunctionOptTranslator functionOpt = new FunctionOptTranslator(this, this, this, sortPolicy, true);
        OrderingModuleOptTranslator orderingModuleOpt = new OrderingModuleOptTranslator(this, this, sortPolicy);
        MembershipPredicateOptTranslator membershipPredOpt = new MembershipPredicateOptTranslator(
                this, sortPolicy, sigAxioms);
        DefaultTranslator defaultTranslator = new DefaultTranslator(this, scopeAxiomStrategy, sigAxioms, sortPolicy);

        List<ScopeExpansionMarker> scopeExpansionMarkers = new ArrayList<>();
        scopeExpansionMarkers.add(defaultTranslator);

        if (options.enableMembershipPredicateOptimization) {
            passes.add(membershipPredOpt.getApplicabilityDeterminingPass(scopeExpansionMarkers));
        }
        passes.add(new TranslationPass(this, sortPolicy, sigAxioms));

        if (options.enableSimpleScalarOptimization) {
            translators.add(new SimpleScalarOptTranslator(this, this));
        }
        if (options.enableOrderingModuleOptimization) {
            translators.add(orderingModuleOpt);
        }
        if (options.enableOneSigOptimization) {
            translators.add(oneSigOpt);
        }
        translators.add(functionOpt);
        if (options.enableJoinOptimization) {
            translators.add(new JoinOptTranslator(this, this));
        }
        if (options.enableMembershipPredicateOptimization) {
            translators.add(membershipPredOpt);
        }
        if (options.enableKodkodIntCompatibility) {
            translators.add(new KodkodIntCompatibilityTranslator(this, sortPolicy));
        }
        translators.add(defaultTranslator);

        if (options.enableOrderingModuleOptimization) {
            scalarCasters.add(orderingModuleOpt);
        }
        if (options.enableOneSigOptimization) {
            scalarCasters.add(oneSigOpt);
        }
        scalarCasters.add(functionOpt);
        scalarCasters.add(new DefaultScalarCaster(this, this, sortPolicy));
        if (options.enableElementOfScalarOptimization) {
            scalarCasters.add(new ElementOfScalarCaster(this, sortPolicy, statistics));
        }

        if (options.enableOneSigOptimization) {
            evaluators.add(oneSigOpt);
        }
        evaluators.add(functionOpt);
        if (options.enableMembershipPredicateOptimization) {
            evaluators.add(membershipPredOpt);
        }
        evaluators.add(defaultTranslator);
        evaluators.add(new SimpleEvaluator(this));
        evaluators.add(new BruteForceEvaluator(this, sortPolicy));
    }

    @Override
    public String name() {
        return "Root";
    }

    /**
     * Perform the entire translation by running through all passes.
     */
    public void runAllPasses(Iterable<Sig> sigs, Command command, ScopeComputer scoper, TranslationContext context) {
        for (Pass pass : passes) {
            pass.performPass(sigs, command, scoper, context);
        }
    }

    /**
     * Translate an expression by delegating to the list of translators.
     * @return The Fortress term for the Alloy expression, as translated by some translator.
     * @throws ErrorFatal If no translator implements a translation for this expression.
     */
    @Override
    public Term translate(Expr expr, TranslationContext context) throws Err {
        if (useCaching) {
            // Try the cache if possible.
            // There's no separate "has" to avoid recomputing the cache key.
            Term cached = translationCache.get(expr, context);
            if (cached != null) {
                // Cache hit!
                statistics.translationCacheHitCount.increment();
                return cached;
            }
        }

        for (Translator translator : translators) {
            Term attempt = translator.translate(expr, context);
            if (attempt != null) {
                statistics.translatorUsageCounts.increment(translator);
                if (useCaching) {
                    translationCache.put(expr, context, attempt);
                }
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
        if (useCaching) {
            Pair<AnnotatedTerm, Term> cached = castToScalarCache.get(expr, context);
            if (cached != null) {
                statistics.castToScalarCacheHitCount.increment();
                return cached;
            }
        }

        for (ScalarCaster scalarCaster : scalarCasters) {
            Pair<AnnotatedTerm, Term> attempt = scalarCaster.castToScalar(expr, context);
            if (attempt != null) {
                statistics.scalarCasterUsageCounts.increment(scalarCaster);
                if (useCaching) {
                    castToScalarCache.put(expr, context, attempt);
                }
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
