package ca.uwaterloo.watform.portus.deltadebug;

import java.util.List;

@FunctionalInterface
public interface Mutation {
    List<State> mutate(State state);
}
