package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A list of Fortress variables annotated with their sorts, with a bunch of convenience methods.
 */
final class VarTuple {

    private final ConstList<AnnotatedVar> vars;

    public VarTuple(Iterable<AnnotatedVar> vars) {
        this.vars = ConstList.make(vars);
    }

    public VarTuple(AnnotatedVar... vars) {
        this(Arrays.asList(vars));
    }

    public ConstList<Var> getVars() {
        return ConstList.make(vars.stream().map(AnnotatedVar::variable).collect(Collectors.toList()));
    }

    public Var getVar(int idx) {
        return getAnnotatedVar(idx).variable();
    }

    public ConstList<AnnotatedVar> getAnnotatedVars() {
        return vars;
    }

    public AnnotatedVar getAnnotatedVar(int idx) {
        return vars.get(idx);
    }

    public ConstList<Sort> getSorts() {
        return ConstList.make(vars.stream().map(AnnotatedVar::sort).collect(Collectors.toList()));
    }

    public Sort getSort(int idx) {
        return getAnnotatedVar(idx).sort();
    }

    public int size() {
        return vars.size();
    }

    public VarTuple concat(VarTuple tuple) {
        // our vars and then their vars
        return new VarTuple(Stream.concat(vars.stream(), tuple.vars.stream()).collect(Collectors.toList()));
    }

    public VarTuple slice(int fromInclusive, int toExclusive) {
        return new VarTuple(new ArrayList<>(vars.subList(fromInclusive, toExclusive)));
    }

    public VarTuple pick(int idx) {
        return slice(idx, idx + 1);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        VarTuple varTuple = (VarTuple) o;
        return Objects.equals(vars, varTuple.vars);
    }

    @Override
    public int hashCode() {
        return Objects.hash(vars);
    }

}
