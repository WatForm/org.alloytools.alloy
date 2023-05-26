package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.translator.A4TupleSet;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Term;
import fortress.msfol.Value;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A set of Fortress tuples, for use when evaluating. Immutable.
 * This is like Kodkod's TupleSet class but not Kodkod-specific.
 */
class TupleSet {

    private final Set<List<Value>> tuples;
    private final int arity;

    public TupleSet(Set<List<Value>> tuples, int arity) {
        this.tuples = tuples;
        this.arity = arity;

        if (arity < 0) {
            throw new ErrorFatal("TupleSet cannot have negative arity!");
        }
        for (List<Value> tuple : tuples) {
            if (tuple.size() != arity) {
                throw new ErrorFatal("All tuples must have the given arity!");
            }
        }
    }

    public static TupleSet empty(int arity) {
        return new TupleSet(Collections.emptySet(), arity);
    }

    public static TupleSet singleton(List<Value> tuple) {
        return new TupleSet(Collections.singleton(tuple), tuple.size());
    }

    public static TupleSet singleton(Value value) {
        return singleton(Collections.singletonList(value));
    }

    public static TupleSet from(Set<List<Value>> tuples) {
        if (tuples.size() == 0) {
            throw new IllegalArgumentException("Cannot infer arity from empty list of tuples!");
        }
        int arity = tuples.iterator().next().size(); // just pick any
        return new TupleSet(tuples, arity);
    }

    public static TupleSet fromScala(
            scala.collection.immutable.Set<scala.collection.immutable.Seq<Value>> tuples, int arity) {
        // Convert from Scala manually to avoid type nonsense
        Set<List<Value>> javaTuples = new HashSet<>();
        tuples.foreach(tuple -> {
            List<Value> javaTuple = new ArrayList<>();
            tuple.foreach(javaTuple::add);
            return javaTuples.add(javaTuple);
        });
        return new TupleSet(javaTuples, arity);
    }

    private void assertCompatible(TupleSet other) {
        Objects.requireNonNull(other);
        if (other.arity != arity) {
            throw new ErrorFatal("Incompatible tuple sets!");
        }
    }

    public TupleSet union(TupleSet other) {
        assertCompatible(other);
        return new TupleSet(SetOps.union(tuples, other.tuples), arity);
    }

    public TupleSet intersection(TupleSet other) {
        assertCompatible(other);
        return new TupleSet(SetOps.intersection(tuples, other.tuples), arity);
    }

    public TupleSet difference(TupleSet other) {
        assertCompatible(other);
        return new TupleSet(SetOps.difference(tuples, other.tuples), arity);
    }

    public TupleSet cartesianProduct(TupleSet other) {
        Objects.requireNonNull(other);
        return new TupleSet(SetOps.cartesianProduct(tuples, other.tuples), arity + other.arity);
    }

    public TupleSet join(TupleSet other) {
        Objects.requireNonNull(other);
        if (arity == 0 || other.arity == 0) {
            throw new ErrorFatal("Cannot join a tuple with arity 0!");
        }
        return new TupleSet(SetOps.join(tuples, other.tuples), arity + other.arity - 1);
    }

    public TupleSet override(TupleSet other) {
        assertCompatible(other);
        if (arity == 0) {
            throw new ErrorFatal("Cannot override tuples with arity 0!");
        }
        return new TupleSet(SetOps.override(tuples, other.tuples), arity);
    }

    public TupleSet transpose() {
        if (arity != 2) {
            throw new ErrorFatal("Can only transpose TupleSets with arity 2!");
        }
        return new TupleSet(SetOps.transpose(tuples), arity);
    }

    public TupleSet transitiveClosure() {
        if (arity != 2) {
            throw new ErrorFatal("Can only take closure of TupleSets with arity 2!");
        }

        // Iterative squaring with fixpoint - this definitely isn't fast but our instances are small
        TupleSet result = this;
        TupleSet last = null;
        while (!result.equals(last)) {
            last = result;
            result = result.union(result.join(this));
        }
        return result;
    }

    public int arity() {
        return arity;
    }

    public int size() {
        return tuples.size();
    }

    public Stream<Value> singleValueStream() {
        if (arity != 1) {
            throw new ErrorFatal("Can only get stream of single values of an arity-1 TupleSet!");
        }
        return tuples.stream().map(tuple -> tuple.get(0));
    }

    public Stream<List<Value>> stream() {
        return tuples.stream();
    }

    public static Collector<List<Value>, ?, TupleSet> collect(int arity) {
        return Collectors.collectingAndThen(Collectors.<List<Value>>toSet(), tuples -> new TupleSet(tuples, arity));
    }

    /** Return whether this TupleSet is of the form {(x)} for some Value x. */
    public boolean isSingleton() {
        return arity == 1 && size() == 1;
    }

    /** Assuming this TupleSet is of the form {(x)}, get x. */
    public Value getSingletonValue() {
        if (!isSingleton()) {
            throw new ErrorFatal("Cannot get singleton value of a non-singleton set!");
        }
        // We know tuples is a singleton set, so just get any value.
        return tuples.iterator().next().get(0);
    }

    /** Return whether this TupleSet is of the form {(Top)} or {(Bottom)}. */
    public boolean isPureBoolean() {
        if (!isSingleton()) return false;
        Value singletonValue = getSingletonValue();
        return singletonValue == Term.mkTop() || singletonValue == Term.mkBottom();
    }

    /** Assuming this TupleSet is a pure boolean, get its value as a Java boolean. */
    public boolean getPureBoolean() {
        if (!isPureBoolean()) {
            throw new ErrorFatal("Cannot get boolean value of a non-pure-boolean set!");
        }
        Value pureBooleanValue = getSingletonValue();
        return pureBooleanValue == Term.mkTop();
    }

    /** Return whether this TupleSet is of the form {(n)} for some integer n. */
    public boolean isPureInt() {
        if (!isSingleton()) return false;
        Value singletonValue = getSingletonValue();
        return singletonValue instanceof IntegerLiteral;
    }

    /** Assuming this TupleSet is a pure int, get its value as a Java int. */
    public int getPureInt() {
        if (!isPureInt()) {
            throw new ErrorFatal("Cannot get int value of a non-pure-int set!");
        }
        IntegerLiteral pureIntValue = (IntegerLiteral) getSingletonValue();
        return pureIntValue.value();
    }

    /**
     * Convert this TupleSet to an A4TupleSet for use with Alloy.
     * Note: if this TupleSet contains a boolean, this will fail!
     */
    public A4TupleSet toAlloy(FortressSolution solution) {
        TupleFactory factory = solution.getUniverse().factory();
        List<Tuple> kodkodTuples = tuples.stream()
                .map(this::convertTupleToKodkod)
                .map(factory::tuple)
                .collect(Collectors.toList());

        kodkod.instance.TupleSet result;
        if (kodkodTuples.isEmpty()) {
            // TupleFactory.setOf() can't determine the arity if there are no tuples
            result = factory.noneOf(arity);
        } else {
            result = factory.setOf(kodkodTuples);
        }
        return new A4TupleSet(result, solution);
    }

    private List<Object> convertTupleToKodkod(List<Value> values) {
        return values.stream()
                .map(this::convertValueToKodkod)
                .collect(Collectors.toList());
    }

    private Object convertValueToKodkod(Value value) {
        // For most atoms, Kodkod accepts any object, but for ints, it expects Java native ints.
        // So convert if necessary.
        if (value instanceof IntegerLiteral) {
            return ((IntegerLiteral) value).value();
        } else if (value == Term.mkTop() || value == Term.mkBottom()) {
            // Booleans aren't valid Kodkod tuple values (they're treated specially),
            // so we need to handle them specially
            throw new ErrorFatal("Booleans are not valid in Kodkod tuples!");
        } else {
            return value;
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TupleSet tupleSet = (TupleSet) o;
        return arity == tupleSet.arity && Objects.equals(tuples, tupleSet.tuples);
    }

    @Override
    public int hashCode() {
        return Objects.hash(tuples, arity);
    }

    @Override
    public String toString() {
        return "TupleSet[" + arity + "]{" +
                tuples.stream()
                        .map(values -> "(" +
                                values.stream()
                                        .map(Object::toString)
                                        .collect(Collectors.joining(", ")) +
                                ")")
                        .collect(Collectors.joining(", ")) +
                "}";
    }

}
