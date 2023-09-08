package ca.uwaterloo.watform.portus.deltadebug;

@FunctionalInterface
public interface Indicator {
    boolean exhibitsBehavior(AlloyInput input);
}
