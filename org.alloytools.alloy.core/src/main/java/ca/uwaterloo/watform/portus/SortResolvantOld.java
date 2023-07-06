package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.Sort;

import java.util.Collections;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

final class SortResolvantOld {

    private final Set<Sort> sorts;

    public static SortResolvantOld NONE = new SortResolvantOld(Collections.emptySet());

    public static SortResolvantOld univ(SortPolicy sortPolicy) {
        return new SortResolvantOld(new HashSet<>(sortPolicy.getAllSorts()));
    }

    public static SortResolvantOld definite(Sort sort) {
        return new SortResolvantOld(Collections.singleton(sort));
    }

    private SortResolvantOld(Set<Sort> sorts) {
        this.sorts = Collections.unmodifiableSet(sorts);
    }

    public boolean isDefinite() {
        return sorts.size() == 1;
    }

    public Sort getDefiniteSort() {
        if (!isDefinite()) {
            throw new ErrorFatal("Cannot get definite sort of indefinite SortResolvant!");
        }
        return sorts.iterator().next(); // get the only element
    }

    public boolean isNone() {
        return sorts.isEmpty();
    }

    public Set<Sort> getAllSorts() {
        return sorts;
    }

    public SortResolvantOld union(SortResolvantOld other) {
        return new SortResolvantOld(SetOps.union(sorts, other.sorts));
    }

    public SortResolvantOld intersection(SortResolvantOld other) {
        return new SortResolvantOld(SetOps.intersection(sorts, other.sorts));
    }

    /** Is there any possible overlap between our sorts and other's sorts? */
    public boolean isDisjoint(SortResolvantOld other) {
        return Collections.disjoint(sorts, other.sorts);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SortResolvantOld that = (SortResolvantOld) o;
        return Objects.equals(sorts, that.sorts);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sorts);
    }

    @Override
    public String toString() {
        return "SortResolvant{" + sorts + "}";
    }

}
