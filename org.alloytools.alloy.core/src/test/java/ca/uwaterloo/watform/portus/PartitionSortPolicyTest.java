package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class PartitionSortPolicyTest {

    private ScopeComputer mockScoper;

    private Command makeCommand(Expr formula) {
        return new Command(false, 0, 4, 4, -1, -1, ExprVar.make(null, "run"), formula);
    }

    private Command makeEmptyCommand() {
        return makeCommand(ExprConstant.TRUE);
    }

    private Sig.PrimSig makeChild(@SuppressWarnings("SameParameterValue") String name, Sig parent) {
        return new Sig.PrimSig(null, name, new Pos(null, 0, 0), (Sig.PrimSig) parent);
    }

    @Before
    public void setUp() {
        mockScoper = mock(ScopeComputer.class);
    }

    @Test
    public void testSingleSig() {
        Sig sig = new Sig.PrimSig("Sig");
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(false);

        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Collections.singletonList(sig), makeEmptyCommand(), mockScoper);

        Sort sort = sortPolicy.getSort(sig);
        assertNotNull(sort);
        assertEquals(2, sortPolicy.getSortScope(sort));
        assertTrue(sortPolicy.isSigEntireSort(sig));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testTwoTopLevelSigs() {
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeEmptyCommand(), mockScoper);

        Sort sortA = sortPolicy.getSort(sigA);
        Sort sortB = sortPolicy.getSort(sigB);
        assertNotNull(sortA);
        assertNotNull(sortB);
        assertNotEquals(sortA, sortB);
        assertEquals(2, sortPolicy.getSortScope(sortA));
        assertEquals(2, sortPolicy.getSortScope(sortB));
        assertTrue(sortPolicy.isSigEntireSort(sigA));
        assertTrue(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sortA, sortB, Sort.Int()));
    }

    @Test
    public void testOneTopLevelSigOneChildSigNonExact() {
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = makeChild("Child", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(4);
        when(mockScoper.isExact(parent)).thenReturn(false);
        when(mockScoper.sig2scope(child)).thenReturn(2);
        when(mockScoper.isExact(child)).thenReturn(false);
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(parent, child), makeEmptyCommand(), mockScoper);

        Sort sort = sortPolicy.getSort(parent);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(child));
        assertEquals(4, sortPolicy.getSortScope(sort));
        // Parent is *not* the entire sort because it's non-exact and has children for reasons explained
        // in a comment in isSigEntireSort
        assertFalse(sortPolicy.isSigEntireSort(parent));
        assertFalse(sortPolicy.isSigEntireSort(child));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testOneTopLevelSigOneChildSigExact() {
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = makeChild("Child", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(4);
        when(mockScoper.isExact(parent)).thenReturn(true);
        when(mockScoper.sig2scope(child)).thenReturn(2);
        when(mockScoper.isExact(child)).thenReturn(false);
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(child, parent), makeEmptyCommand(), mockScoper);

        Sort sort = sortPolicy.getSort(parent);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(child));
        assertEquals(4, sortPolicy.getSortScope(sort));
        // Parent *is* the entire sort even though it has children because it's exact
        assertTrue(sortPolicy.isSigEntireSort(parent));
        assertFalse(sortPolicy.isSigEntireSort(child));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeQuantifier() {
        // test they merge upon [[forall x: A+B | true]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        Expr formula = ExprConstant.TRUE.forAll(sigA.plus(sigB).oneOf("x"));
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeCommand(formula), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeQuantifiedExpr() {
        // test they merge upon [[some A+B]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        Expr formula = sigA.plus(sigB).some();
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeCommand(formula), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeOverride() {
        // test they merge upon appearing on the RHS of an override after first position: [[e ++ (A->A+B)]]
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        Expr formula = ExprVar.make(null, "e", Type.make(sigA).product(Type.make(sigA)))
                .override(sigA.product(sigA.plus(sigB)));
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeCommand(formula), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeWithinLet() {
        // test they can still merge correctly in the presence of lets: [[let a=A | no (a+B)]] merges
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        ExprVar a = ExprVar.make(null, "a");
        Expr formula = ExprLet.make(null, a, sigA, a.plus(sigB).no());
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeCommand(formula), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeWithinField() {
        // test merge within field bound exprs: "f: A+B" merges
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        sigA.addField("f", sigA.plus(sigB));
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigA, sigB), makeEmptyCommand(), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testMergeSubsetSig() {
        // test that a subset sig "sig AB in A + B" causes its parents to merge
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockScoper.sig2scope(sigA)).thenReturn(2);
        when(mockScoper.isExact(sigA)).thenReturn(false);
        when(mockScoper.sig2scope(sigB)).thenReturn(2);
        when(mockScoper.isExact(sigB)).thenReturn(false);

        Sig.SubsetSig sigC = new Sig.SubsetSig(null, "C",
                Arrays.asList(new Pos(null, 0, 0), new Pos(null, 0, 0)),
                Arrays.asList(sigA, sigB));
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Arrays.asList(sigC, sigA, sigB), makeEmptyCommand(), mockScoper);

        Sort sort = sortPolicy.getSort(sigA);
        assertNotNull(sort);
        assertEquals(sort, sortPolicy.getSort(sigB));
        assertEquals(sort, sortPolicy.getSort(sigC));
        assertEquals(4, sortPolicy.getSortScope(sort));
        assertFalse(sortPolicy.isSigEntireSort(sigA));
        assertFalse(sortPolicy.isSigEntireSort(sigB));
        assertFalse(sortPolicy.isSigEntireSort(sigC));
        assertThat(sortPolicy.getAllSorts(), containsInAnyOrder(sort, Sort.Int()));
    }

    @Test
    public void testBuiltins() {
        PartitionSortPolicy sortPolicy = new PartitionSortPolicy(
                Collections.emptyList(), makeEmptyCommand(), mockScoper);
        assertEquals(Sort.Int(), sortPolicy.getSort(Sig.SIGINT));
        assertEquals(Sort.Int(), sortPolicy.getSort(Sig.SEQIDX));
        assertNull(sortPolicy.getSort(Sig.UNIV));
        assertNull(sortPolicy.getSort(Sig.NONE));

        when(mockScoper.getBitwidth()).thenReturn(3);
        assertEquals(8, sortPolicy.getSortScope(Sort.Int()));

        assertTrue(sortPolicy.isSigEntireSort(Sig.SIGINT));
        assertFalse(sortPolicy.isSigEntireSort(Sig.SEQIDX));
        assertFalse(sortPolicy.isSigEntireSort(Sig.UNIV));
        assertFalse(sortPolicy.isSigEntireSort(Sig.NONE));
    }

}
