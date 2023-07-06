package ca.uwaterloo.watform.portus;

import fortress.msfol.Sort;

import java.util.List;
import java.util.Set;

final class SortResolvant {

    private final Set<List<Sort>> sortTuples;
    private final int arity;

    private SortResolvant(Set<List<Sort>> sortTuples, int arity) {
        for (List<Sort> tuple : sortTuples) {
            if (tuple.size() != arity) {
                throw new IllegalArgumentException("Tuple does not match arity!");
            }
        }

        this.sortTuples = sortTuples;
        this.arity = arity;
    }

}
