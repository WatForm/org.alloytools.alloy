package ca.uwaterloo.watform.portus;

import fortress.msfol.Sort;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

final class SortResolvant {

    private final TupleSet<Sort> sortTuples;

    private SortResolvant(TupleSet<Sort> sortTuples) {
        Objects.requireNonNull(sortTuples);
        this.sortTuples = sortTuples;
    }

    public static SortResolvant NONE = new SortResolvant(TupleSet.empty(1));

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

    public static SortResolvant definite(Sort sort) {
        return new SortResolvant(TupleSet.singleton(sort));
    }

    public boolean isDefinite() {
        return sortTuples.isSingleton();
    }

    public Sort getDefiniteSort() {
        return sortTuples.getSingleton();
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

}
