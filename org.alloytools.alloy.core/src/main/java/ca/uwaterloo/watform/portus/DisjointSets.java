package ca.uwaterloo.watform.portus;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * An implementation of the union-find data structure, also known as a disjoint set data structure.
 * The data structure keeps track of a partition of a set and allows efficient joining of sets and querying which set
 * an element is in.
 * See https://en.wikipedia.org/wiki/Disjoint-set_data_structure.
 */
final class DisjointSets<T> {

    // We use integers from 0 to numElements-1 to represent the sets and the elements.
    // Each element is associated with an integer, so we don't have to keep computing hashes.
    private final Map<T, Integer> elementToIndex = new HashMap<>();

    // The data structure works like this: each set has a representative.
    // The representative of a set is the unique element x in the set such that tree[x] = x.
    // Other elements of the set either have tree[x] equal to the representative, or to another element of the set
    // higher in a tree rooted at the representative.
    // Two elements are in the same set if and only if they have the same representative, following tree.
    // To unite two sets, take their representatives x, y and set tree[x] = y or vice versa.
    private final int[] tree;

    // Keep track of how many elements are in each set. This is used for efficient uniting but also other purposes.
    // This array only stores valid sizes for the representatives of each set.
    private final int[] sizes;

    public DisjointSets(List<T> elements) {
        // The number of elements in the underlying set being partitioned.
        int numElements = elements.size();
        for (int i = 0; i < numElements; i++) {
            elementToIndex.put(elements.get(i), i);
        }

        tree = new int[numElements];
        sizes = new int[numElements];
        for (int i = 0; i < numElements; i++) {
            // At the beginning, each element is in its own set of size 1, so it is its own representative.
            tree[i] = i;
            sizes[i] = 1;
        }
    }

    /** Return the representative of the set index is in. */
    private int find(int index) {
        if (tree[index] == index) {
            // It's its own representative
            return index;
        } else {
            // Recurse up the tree, and set tree[index] equal to the representative so it's faster next time
            return tree[index] = find(tree[index]);
        }
    }

    /** Unite the sets corresponding to index1 and index2. */
    private void unite(int index1, int index2) {
        int repr1 = find(index1);
        int repr2 = find(index2);

        // Union by size: the new representative is the one from the larger set.
        int largerRepr, smallerRepr;
        if (sizes[repr1] > sizes[repr2]) {
            largerRepr = repr1;
            smallerRepr = repr2;
        } else {
            largerRepr = repr2;
            smallerRepr = repr1;
        }

        tree[smallerRepr] = largerRepr;
        sizes[largerRepr] += sizes[smallerRepr];
    }

    /**
     * Unite (merge) the sets the two elements are in.
     * @throws NoSuchElementException If either element is not in the set.
     */
    public void unite(T element1, T element2) {
        if (!elementToIndex.containsKey(element1) || !elementToIndex.containsKey(element2)) {
            throw new NoSuchElementException();
        }
        unite(elementToIndex.get(element1), elementToIndex.get(element2));
    }

    /**
     * Get the disjoint set containing the element.
     * @throws NoSuchElementException If the element is not in the set.
     */
    public Set<T> getSet(T element) {
        if (!elementToIndex.containsKey(element)) {
            throw new NoSuchElementException();
        }

        // O(n), but that's okay
        Set<T> set = new HashSet<>();
        int representative = find(elementToIndex.get(element));

        for (T el : elementToIndex.keySet()) {
            if (find(elementToIndex.get(el)) == representative) {
                set.add(el);
            }
        }

        return set;
    }

    /**
     * Return whether element1 and element2 are in the same set.
     */
    public boolean areSameSet(T element1, T element2) {
        if (!elementToIndex.containsKey(element1) || !elementToIndex.containsKey(element2)) {
            throw new NoSuchElementException();
        }
        return find(elementToIndex.get(element1)) == find(elementToIndex.get(element2));
    }

}
