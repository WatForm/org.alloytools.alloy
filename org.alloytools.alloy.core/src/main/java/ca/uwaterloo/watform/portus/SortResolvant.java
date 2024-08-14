package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.Sort;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A model of the sorts assigned to an expression as a set of tuples of sorts.
 * E.g., "(A+B)->(C+D)" would get sorts {(A,C), (A,D), (B,C), (B, D)}.
 * We do it this way so we can model iden.
 */
final class SortResolvant {

    private final TupleSet<Sort> sortTuples;

    private SortResolvant(TupleSet<Sort> sortTuples) {
        Objects.requireNonNull(sortTuples);
        this.sortTuples = sortTuples;
    }

    public static final SortResolvant NONE = none(1);

    public static SortResolvant none(int size) {
        return new SortResolvant(TupleSet.empty(size));
    }

    public static SortResolvant univ(SortPolicy sortPolicy) {
        return new SortResolvant(TupleSet.singletons(sortPolicy.getAllSorts()));
    }

    public static SortResolvant iden(SortPolicy sortPolicy) {
        List<Sort> sorts = sortPolicy.getAllSorts();
        Set<List<Sort>> sortPairs = sorts.stream()
                .map(sort -> Arrays.asList(sort, sort))
                .collect(Collectors.toSet());
        return new SortResolvant(new TupleSet<>(sortPairs, 2));
    }

    public static SortResolvant definite(List<Sort> sorts) {
        return new SortResolvant(TupleSet.singleton(sorts));
    }

    public static SortResolvant definite(Sort... sorts) {
        return SortResolvant.definite(Arrays.asList(sorts));
    }

    public static SortResolvant singleColumn(Set<Sort> sorts) {
        return new SortResolvant(TupleSet.singletons(sorts));
    }

    public int arity() {
        return sortTuples.arity();
    }

    public boolean isDefinite() {
        return sortTuples.isSingleTuple();
    }

    public List<Sort> getDefiniteSorts() {
        return sortTuples.getSingleTuple();
    }

    /**
     * Get a list of all the sorts that could appear in a column, forgetting
     * their relationships with sorts in other columns.
     */
    public Set<Sort> getSortsInColumn(int column) {
        if (column < 0 || column >= arity()) {
            throw new ErrorFatal("Column " + column + " out of range for getSortsInColumn!");
        }
        return sortTuples.stream()
                .map(tuple -> tuple.get(column))
                .collect(Collectors.toSet());
    }

    public Stream<List<Sort>> stream() {
        return sortTuples.stream();
    }

    public SortResolvant filter(Predicate<List<Sort>> predicate) {
        return new SortResolvant(stream().filter(predicate).collect(TupleSet.collect(arity())));
    }

    public boolean isNone() {
        return sortTuples.isEmpty();
    }

    public SortResolvant union(SortResolvant other) {
        return new SortResolvant(sortTuples.union(other.sortTuples));
    }

    public SortResolvant intersection(SortResolvant other) {
        return new SortResolvant(sortTuples.intersection(other.sortTuples));
    }

    public SortResolvant cartesianProduct(SortResolvant other) {
        return new SortResolvant(sortTuples.cartesianProduct(other.sortTuples));
    }

    public SortResolvant join(SortResolvant other) {
        return new SortResolvant(sortTuples.join(other.sortTuples));
    }

    public SortResolvant domainRestrict(SortResolvant other) {
        if (other.arity() != 1) {
            throw new ErrorFatal("Domain-restriction argument must have arity 1!");
        }
        return new SortResolvant(sortTuples.domainRestrict(other.sortTuples));
    }

    public SortResolvant rangeRestrict(SortResolvant other) {
        if (other.arity() != 1) {
            throw new ErrorFatal("Range-restriction argument must have arity 1!");
        }
        return new SortResolvant(sortTuples.rangeRestrict(other.sortTuples));
    }

    public SortResolvant transpose() {
        return new SortResolvant(sortTuples.transpose());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SortResolvant that = (SortResolvant) o;
        return sortTuples.equals(that.sortTuples);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sortTuples);
    }

    @Override
    public String toString() {
        return "SortResolvant{" + sortTuples + '}';
    }

}
