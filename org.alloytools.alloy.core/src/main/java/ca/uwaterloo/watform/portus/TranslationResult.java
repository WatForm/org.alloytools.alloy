package ca.uwaterloo.watform.portus;

import fortress.modelfinders.ModelFinder;
import fortress.msfol.Sort;
import fortress.msfol.Theory;
import fortress.problemstate.ProblemState;
import fortress.problemstate.Scope;

/**
 * A container for results from the Portus translation. From this you can run the SMT solver.
 */
public final class TranslationResult {

    private final Evaluator evaluator;
    private final StringDecoder stringDecoder;
    private final SortPolicy sortPolicy;
    private final TranslationContext context;

    TranslationResult(Evaluator evaluator, StringDecoder stringDecoder, SortPolicy sortPolicy,
                      TranslationContext context) {
        this.stringDecoder = stringDecoder;
        this.evaluator = evaluator;
        this.sortPolicy = sortPolicy;
        this.context = context;
    }

    /**
     * Get the Fortress theory output by Portus.
     */
    public Theory getTheory() {
        return context.getTheory();
    }

    /**
     * Get the bitwidth of the model.
     */
    public int getBitwidth() {
        return context.getBitwidth();
    }

    /**
     * Convert a theory to a problem state given our sort policy.
     */
    public ProblemState getProblemState(Theory theory) {
        return ProblemState.apply(theory,
                PortusUtil.<Sort, Scope>toScalaMap(context.getSortToScopeMap(sortPolicy)), false);
    }

    /**
     * Get the Evaluator used to evaluate Alloy expressions in the theory.
     */
    Evaluator getEvaluator() {
        return evaluator;
    }

    /**
     * Get the StringDecoder used to determine the value of string constants.
     */
    StringDecoder getStringDecoder() {
        return stringDecoder;
    }

    /**
     * Get the saved context from the translation.
     */
    TranslationContext getContext() {
        return context;
    }

    /**
     * Get the scope of a sort in the theory.
     */
    public int getSortScope(Sort sort) {
        return sortPolicy.getSortScope(sort);
    }

    /**
     * Configure a model finder to solve on this translated model.
     */
    public void configureModelFinder(ModelFinder finder) {
        context.configureModelFinder(finder, sortPolicy);
    }

}
