package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.ast.Expr;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public final class AlloyDeltaDebugger {

    private static final List<Mutation> DEFAULT_MUTATIONS = Arrays.asList(
            ChildrenMutation.AND_OR,
            ChildrenMutation.BINARY,
            ChildrenMutation.UNARY,
            ChildrenMutation.QUANTIFIER,
            ChildrenMutation.ITE);

    private final List<Mutation> mutations;

    public AlloyDeltaDebugger(List<Mutation> mutations) {
        this.mutations = mutations;
    }

    public AlloyDeltaDebugger() {
        this(DEFAULT_MUTATIONS);
    }

    private State deltaDebugImpl(Indicator indicator, State state) {
        // Just recurse in the first one that returns something to minimize calls to the indicator
        // TODO: parallelism?
        for (Mutation mutation : mutations) {
            List<State> children = mutation.mutate(state);
            for (State child : children) {
                if (indicator.exhibitsBehavior(child.toInput())) {
                    return deltaDebugImpl(indicator, child);
                }
            }
        }

        // None of them did - recurse over all the children of the current expr
        // Don't stop after one of them returns something (we wouldn't know) in order to minimize for all children
        List<Expr> newCurrentFormulaChildren = state.getChildren().stream()
                .map(child -> deltaDebugImpl(indicator, child))
                .map(childState -> childState.currentSubformula)
                .collect(Collectors.toList());
        return state.replaceCurrentSubformula(
                ASTUtil.replaceChildren(state.currentSubformula, newCurrentFormulaChildren));
    }

    public AlloyInput deltaDebug(Indicator indicator, AlloyInput input) {
        State initialState = new State(input);
        State finalState = deltaDebugImpl(indicator, initialState);
        return finalState.toInput();
    }

}
