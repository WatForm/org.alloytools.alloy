package ca.uwaterloo.watform.portus;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Utilities for manipulating sets (and lists) in an immutable, functional manner.
 * Each function returns a new set (or list) and does not modify its input.
 */
final class SetOps {

    public static <T> Set<T> add(Set<T> set, T value) {
        Set<T> result = new HashSet<>(set);
        result.add(value);
        return result;
    }

    public static <T> Set<T> union(Set<T> a, Set<T> b) {
        Set<T> result = new HashSet<>(a);
        result.addAll(b);
        return result;
    }

    public static <T> Set<T> intersection(Set<T> a, Set<T> b) {
        Set<T> result = new HashSet<>(a);
        result.retainAll(b);
        return result;
    }

    public static <T> Set<T> difference(Set<T> a, Set<T> b) {
        Set<T> result = new HashSet<>(a);
        result.removeAll(b);
        return result;
    }

    public static <T> boolean subset(Set<T> a, Set<T> b) {
        return b.containsAll(a);
    }

    public static <T> Set<List<T>> cartesianProduct(Set<List<T>> a, Set<List<T>> b) {
        Set<List<T>> result = new HashSet<>();
        for (List<T> aTuple : a) {
            for (List<T> bTuple : b) {
                result.add(concatenate(aTuple, bTuple));
            }
        }
        return result;
    }

    // TODO: These assume there are no 0-tuples, is that true?

    public static <T> Set<List<T>> join(Set<List<T>> a, Set<List<T>> b) {
        // TODO: Can this be done more intelligently? Probably not, look at DB literature
        Set<List<T>> result = new HashSet<>();
        for (List<T> aTuple : a) {
            for (List<T> bTuple : b) {
                if (Objects.equals(aTuple.get(aTuple.size() - 1), bTuple.get(0))) {
                    result.add(concatenate(
                            aTuple.subList(0, aTuple.size() - 1),
                            bTuple.subList(1, bTuple.size())));
                }
            }
        }
        return result;
    }

    public static <T> Set<List<T>> override(Set<List<T>> a, Set<List<T>> b) {
        Set<List<T>> result = new HashSet<>(b);

        // Add all tuples from a to result who don't share first elements with a tuple in b
        // Try to be a bit more intelligent about it - O(n) not O(n^2), assuming O(1) set lookup
        Set<T> firstValues = b.stream()
                .map(tuple -> tuple.get(0))
                .collect(Collectors.toSet());
        for (List<T> aTuple : a) {
            if (!firstValues.contains(aTuple.get(0))) {
                result.add(aTuple);
            }
        }

        return result;
    }

    // These assume all are 2-tuples

    public static <T> Set<List<T>> transpose(Set<List<T>> relation) {
        return relation.stream()
                .map(pair -> {
                    assert pair.size() == 2;
                    return Arrays.asList(pair.get(1), pair.get(0));
                })
                .collect(Collectors.toSet());
    }

    // Technically these are list operations and not set operations, but oh well

    public static <T> List<T> concatenate(List<T> a, List<T> b) {
        List<T> result = new ArrayList<>(a);
        result.addAll(b);
        return result;
    }

    public static <T> List<T> concatenate(List<T> list, T value) {
        List<T> result = new ArrayList<>(list);
        result.add(value);
        return result;
    }

}
