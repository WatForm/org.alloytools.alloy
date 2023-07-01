package ca.uwaterloo.watform.portus;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.NoSuchElementException;
import java.util.Set;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.Assert.assertThrows;

public class DisjointSetsTest {

    @Test
    public void testGetSetWithOneElement() {
        DisjointSets<Integer> sets = new DisjointSets<>(Collections.singletonList(1));
        Set<Integer> set = sets.getSet(1);
        assertThat(set, containsInAnyOrder(1));
    }

    @Test
    public void testGetSetWithNonexistentElement() {
        DisjointSets<Integer> sets = new DisjointSets<>(Collections.singletonList(1));
        assertThrows(NoSuchElementException.class, () -> sets.getSet(0));
    }

    @Test
    public void testGetSetWithNoElements() {
        DisjointSets<Integer> sets = new DisjointSets<>(Collections.emptyList());
        assertThrows(NoSuchElementException.class, () -> sets.getSet(1));
    }

    @Test
    public void testGetSetWithTwoElements() {
        DisjointSets<Integer> sets = new DisjointSets<>(Arrays.asList(1, 2));
        assertThat(sets.getSet(1), containsInAnyOrder(1));
        assertThat(sets.getSet(2), containsInAnyOrder(2));
    }

    @Test
    public void testUniteWithTwoElements() {
        DisjointSets<Integer> sets = new DisjointSets<>(Arrays.asList(1, 2));
        sets.unite(1, 2);
        assertThat(sets.getSet(1), containsInAnyOrder(1, 2));
        assertThat(sets.getSet(2), containsInAnyOrder(1, 2));
    }

    @Test
    public void testUniteWithNonexistentElements() {
        DisjointSets<Integer> sets = new DisjointSets<>(Arrays.asList(1, 2));
        assertThrows(NoSuchElementException.class, () -> sets.unite(3, 4));
        assertThrows(NoSuchElementException.class, () -> sets.unite(1, 4));
        assertThrows(NoSuchElementException.class, () -> sets.unite(3, 1));
    }

    @Test
    public void testUniteWithThreeElements() {
        DisjointSets<Integer> sets = new DisjointSets<>(Arrays.asList(1, 2, 3));
        assertThat(sets.getSet(1), containsInAnyOrder(1));
        assertThat(sets.getSet(2), containsInAnyOrder(2));
        assertThat(sets.getSet(3), containsInAnyOrder(3));
        sets.unite(2, 3);
        assertThat(sets.getSet(1), containsInAnyOrder(1));
        assertThat(sets.getSet(2), containsInAnyOrder(2, 3));
        assertThat(sets.getSet(3), containsInAnyOrder(2, 3));
        sets.unite(1, 2);
        assertThat(sets.getSet(1), containsInAnyOrder(1, 2, 3));
        assertThat(sets.getSet(2), containsInAnyOrder(1, 2, 3));
        assertThat(sets.getSet(3), containsInAnyOrder(1, 2, 3));
    }

}
