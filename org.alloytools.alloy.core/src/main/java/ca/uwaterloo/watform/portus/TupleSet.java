package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * An abstract set of tuples, all of which have the same arity.
 */
final class TupleSet<T> {

    private final Set<List<T>> tuples;
    private final int arity;

    public TupleSet(Set<List<T>> tuples, int arity) {
        this.tuples = tuples;
        this.arity = arity;

        if (arity < 0) {
            throw new ErrorFatal("TupleSet<T> cannot have negative arity!");
        }
        for (List<T> tuple : tuples) {
            if (tuple.size() != arity) {
                throw new ErrorFatal("All tuples must have the given arity!");
            }
        }
    }

    public static <T> TupleSet<T> empty(int arity) {
        return new TupleSet<>(Collections.emptySet(), arity);
    }

    /** {(x, y, z, ...)} */
    public static <T> TupleSet<T> singleton(List<T> tuple) {
        return new TupleSet<>(Collections.singleton(tuple), tuple.size());
    }

    /** {(x)} */
    public static <T> TupleSet<T> singleton(T value) {
        return singleton(Collections.singletonList(value));
    }

    /** {(x), (y), (z), ...} */
    public static <T> TupleSet<T> singletons(Iterable<T> atoms) {
        return StreamSupport.stream(atoms.spliterator(), false)
                .map(Collections::singletonList)
                .collect(TupleSet.collect(1));
    }

    public int arity() {
        return arity;
    }

    public int size() {
        return tuples.size();
    }

    private void assertCompatible(TupleSet<T> other) {
        Objects.requireNonNull(other);
        if (arity != other.arity) {
            throw new ErrorFatal("Incompatible tuple sets!");
        }
    }

    public TupleSet<T> union(TupleSet<T> other) {
        assertCompatible(other);
        return new TupleSet<>(SetOps.union(tuples, other.tuples), arity);
    }

    public TupleSet<T> intersection(TupleSet<T> other) {
        assertCompatible(other);
        return new TupleSet<>(SetOps.intersection(tuples, other.tuples), arity);
    }

    public TupleSet<T> difference(TupleSet<T> other) {
        assertCompatible(other);
        return new TupleSet<>(SetOps.difference(tuples, other.tuples), arity);
    }

    public TupleSet<T> cartesianProduct(TupleSet<T> other) {
        Objects.requireNonNull(other);
        return new TupleSet<>(SetOps.cartesianProduct(tuples, other.tuples), arity + other.arity);
    }

    public TupleSet<T> join(TupleSet<T> other) {
        Objects.requireNonNull(other);
        if (arity == 0 || other.arity == 0) {
            throw new ErrorFatal("Cannot join a tuple with arity 0!");
        }
        return new TupleSet<>(SetOps.join(tuples, other.tuples), arity + other.arity - 1);
    }

    public TupleSet<T> override(TupleSet<T> other) {
        assertCompatible(other);
        if (arity == 0) {
            throw new ErrorFatal("Cannot override tuples with arity 0!");
        }
        return new TupleSet<>(SetOps.override(tuples, other.tuples), arity);
    }

    public TupleSet<T> transpose() {
        if (arity != 2) {
            throw new ErrorFatal("Can only transpose TupleSets with arity 2!");
        }
        return new TupleSet<>(SetOps.transpose(tuples), arity);
    }

    public TupleSet<T> transitiveClosure() {
        if (arity != 2) {
            throw new ErrorFatal("Can only take closure of TupleSets with arity 2!");
        }

        // Iterative squaring with fixpoint - this definitely isn't fast but our instances are small
        TupleSet<T> result = this;
        TupleSet<T> last = null;
        while (!result.equals(last)) {
            last = result;
            result = result.union(result.join(this));
        }
        return result;
    }

    public Stream<T> singleValueStream() {
        if (arity != 1) {
            throw new ErrorFatal("Can only get stream of single values of an arity-1 TupleSet!");
        }
        return stream().map(tuple -> tuple.get(0));
    }

    public Stream<List<T>> stream() {
        return tuples.stream();
    }

    public static <T> Collector<List<T>, ?, TupleSet<T>> collect(int arity) {
        return Collectors.collectingAndThen(Collectors.<List<T>>toSet(), tuples -> new TupleSet<>(tuples, arity));
    }

    public boolean isEmpty() {
        return tuples.isEmpty();
    }

    /** Return whether this TupleSet is of the form {(x1,...,xn)} for some x. */
    public boolean isSingleTuple() {
        return size() == 1;
    }

    /** Assuming this TupleSet is of the form {(x1,...,xn)}, get (x1,...,xn). */
    public List<T> getSingleTuple() {
        if (!isSingleTuple()) {
            throw new ErrorFatal("Cannot get single tuple: there is more than one tuple!");
        }
        // Just get anything.
        return tuples.iterator().next();
    }

    /** Return whether this TupleSet is of the form {(x)} for some x. */
    public boolean isSingleton() {
        return arity == 1 && size() == 1;
    }

    /** Assuming this TupleSet is of the form {(x)}, get x. */
    public T getSingleton() {
        if (!isSingleton()) {
            throw new ErrorFatal("Cannot get singleton value of a non-singleton set!");
        }
        // We know tuples is a singleton set, so just get any value.
        return tuples.iterator().next().get(0);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TupleSet<?> tupleSet = (TupleSet<?>) o;
        return arity == tupleSet.arity && tuples.equals(tupleSet.tuples);
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