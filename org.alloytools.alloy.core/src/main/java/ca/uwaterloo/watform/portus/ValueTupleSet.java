package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.translator.A4TupleSet;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Term;
import fortress.msfol.Value;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.ArrayList;
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
final class ValueTupleSet {

    // We mostly delegate to tupleSet with some helper methods on top.
    private final TupleSet<Value> tupleSet;

    private ValueTupleSet(TupleSet<Value> tupleSet) {
        Objects.requireNonNull(tupleSet);
        this.tupleSet = tupleSet;
    }

    public ValueTupleSet(Set<List<Value>> tuples, int arity) {
        this(new TupleSet<>(tuples, arity));
    }

    public static ValueTupleSet empty(int arity) {
        return new ValueTupleSet(TupleSet.empty(arity));
    }

    public static ValueTupleSet singleton(List<Value> tuple) {
        return new ValueTupleSet(TupleSet.singleton(tuple));
    }

    public static ValueTupleSet singleton(Value value) {
        return new ValueTupleSet(TupleSet.singleton(value));
    }

    public static ValueTupleSet atoms(Iterable<Value> atoms) {
        return new ValueTupleSet(TupleSet.singletons(atoms));
    }

    public static ValueTupleSet from(Set<List<Value>> tuples) {
        if (tuples.size() == 0) {
            throw new IllegalArgumentException("Cannot infer arity from empty list of tuples!");
        }
        int arity = tuples.iterator().next().size(); // just pick any
        return new ValueTupleSet(tuples, arity);
    }

    public static ValueTupleSet fromScala(
            scala.collection.immutable.Set<scala.collection.immutable.Seq<Value>> tuples, int arity) {
        // Convert from Scala manually to avoid type nonsense
        Set<List<Value>> javaTuples = new HashSet<>();
        tuples.foreach(tuple -> {
            List<Value> javaTuple = new ArrayList<>();
            tuple.foreach(javaTuple::add);
            return javaTuples.add(javaTuple);
        });
        return new ValueTupleSet(javaTuples, arity);
    }

    public ValueTupleSet union(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.union(other.tupleSet));
    }

    public ValueTupleSet intersection(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.intersection(other.tupleSet));
    }

    public ValueTupleSet difference(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.difference(other.tupleSet));
    }

    public ValueTupleSet cartesianProduct(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.cartesianProduct(other.tupleSet));
    }

    public ValueTupleSet join(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.join(other.tupleSet));
    }

    public ValueTupleSet override(ValueTupleSet other) {
        return new ValueTupleSet(tupleSet.override(other.tupleSet));
    }

    public ValueTupleSet transpose() {
        return new ValueTupleSet(tupleSet.transpose());
    }

    public ValueTupleSet transitiveClosure() {
        return new ValueTupleSet(tupleSet.transitiveClosure());
    }

    public int arity() {
        return tupleSet.arity();
    }

    public int size() {
        return tupleSet.size();
    }

    public boolean isEmpty() {
        return tupleSet.isEmpty();
    }

    public Stream<Value> singleValueStream() {
        return tupleSet.singleValueStream();
    }

    public Stream<List<Value>> stream() {
        return tupleSet.stream();
    }

    public static Collector<List<Value>, ?, ValueTupleSet> collect(int arity) {
        return Collectors.collectingAndThen(TupleSet.collect(arity), ValueTupleSet::new);
    }

    /** Return whether this ValueTupleSet is of the form {(x)} for some Value x. */
    public boolean isSingleton() {
        return tupleSet.isSingleton();
    }

    /** Assuming this ValueTupleSet is of the form {(x)}, get x. */
    public Value getSingletonValue() {
        return tupleSet.getSingleton();
    }

    /** Return whether this ValueTupleSet is of the form {(Top)} or {(Bottom)}. */
    public boolean isPureBoolean() {
        if (!isSingleton()) return false;
        Value singletonValue = getSingletonValue();
        return Objects.equals(singletonValue, Term.mkTop()) || Objects.equals(singletonValue, Term.mkBottom());
    }

    /** Assuming this ValueTupleSet is a pure boolean, get its value as a Java boolean. */
    public boolean getPureBoolean() {
        if (!isPureBoolean()) {
            throw new ErrorFatal("Cannot get boolean value of a non-pure-boolean set!");
        }
        Value pureBooleanValue = getSingletonValue();
        return Objects.equals(pureBooleanValue, Term.mkTop());
    }

    /** Return whether this ValueTupleSet is of the form {(n)} for some integer n. */
    public boolean isPureInt() {
        if (!isSingleton()) return false;
        Value singletonValue = getSingletonValue();
        return singletonValue instanceof IntegerLiteral;
    }

    /** Assuming this ValueTupleSet is a pure int, get its value as a Java int. */
    public int getPureInt() {
        if (!isPureInt()) {
            throw new ErrorFatal("Cannot get int value of a non-pure-int set!");
        }
        IntegerLiteral pureIntValue = (IntegerLiteral) getSingletonValue();
        return pureIntValue.value();
    }

    /**
     * Convert this ValueTupleSet to an A4TupleSet for use with Alloy.
     * Note: if this ValueTupleSet contains a boolean, this will fail!
     */
    public A4TupleSet toAlloy(FortressSolution solution) {
        TupleFactory factory = solution.getUniverse().factory();
        List<Tuple> kodkodTuples = stream()
                .map(this::convertTupleToKodkod)
                .map(factory::tuple)
                .collect(Collectors.toList());

        kodkod.instance.TupleSet result;
        if (kodkodTuples.isEmpty()) {
            // TupleFactory.setOf() can't determine the arity if there are no tuples
            result = factory.noneOf(tupleSet.arity());
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
        } else if (Objects.equals(value, Term.mkTop()) || Objects.equals(value, Term.mkBottom())) {
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
        ValueTupleSet valueTupleSet = (ValueTupleSet) o;
        return tupleSet.equals(valueTupleSet.tupleSet);
    }

    @Override
    public int hashCode() {
        return Objects.hash(tupleSet);
    }

    @Override
    public String toString() {
        return "ValueTupleSet{" + tupleSet + "}";
    }

}
