package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class UnivSortPolicyTest {

    private final Sort univ = Sort.mkSortConst("testUniv");
    private ScopeComputer scoper;

    @Before
    public void setUp() {
        scoper = mock(ScopeComputer.class);
    }

    @Test
    public void testGetSort_normalSig() {
        Sig mySig = new Sig.PrimSig("S");
        SortPolicy policy = new UnivSortPolicy(univ, Collections.singletonList(mySig), scoper);
        assertEquals(univ, policy.getSort(mySig));
    }

    @Test
    public void testGetSort_multipleNormalSigs() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sig sig3 = new Sig.PrimSig("S3");
        SortPolicy policy = new UnivSortPolicy(univ, Arrays.asList(sig1, sig2, sig3), scoper);
        assertEquals(univ, policy.getSort(sig1));
        assertEquals(univ, policy.getSort(sig2));
        assertEquals(univ, policy.getSort(sig3));
    }

    @Test
    public void testGetSort_subSig() {
        Sig.PrimSig parent = new Sig.PrimSig("P");
        Sig.PrimSig child = new Sig.PrimSig(null, "S", new Pos("", 0, 0), parent);
        SortPolicy policy = new UnivSortPolicy(univ, Arrays.asList(parent, child), scoper);
        assertEquals(univ, policy.getSort(parent));
        assertEquals(univ, policy.getSort(child));
    }

    @Test
    public void testGetSort_int() {
        SortPolicy policy = new UnivSortPolicy(univ, new ArrayList<>(), scoper);
        assertEquals(Sort.Int(), policy.getSort(Sig.SIGINT));
    }

    @Test
    public void testGetSort_seqIdx() {
        SortPolicy policy = new UnivSortPolicy(univ, new ArrayList<>(), scoper);
        assertEquals(Sort.Int(), policy.getSort(Sig.SEQIDX));
    }

    @Test
    public void testGetSort_univ() {
        SortPolicy policy = new UnivSortPolicy(univ, new ArrayList<>(), scoper);
        assertNull(policy.getSort(Sig.UNIV));
    }

    @Test
    public void testGetSort_none() {
        SortPolicy policy = new UnivSortPolicy(univ, new ArrayList<>(), scoper);
        assertNull(policy.getSort(Sig.NONE));
    }

    @Test
    public void testGetSortScope_univ() {
        // should be the sum of all sig scopes
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sig sig3 = new Sig.PrimSig("S3");
        when(scoper.sig2scope(sig1)).thenReturn(3);
        when(scoper.sig2scope(sig2)).thenReturn(7);
        when(scoper.sig2scope(sig3)).thenReturn(11);
        SortPolicy policy = new UnivSortPolicy(univ, Arrays.asList(sig1, sig2, sig3), scoper);
        assertEquals(21, policy.getSortScope(univ));
    }

    @Test
    public void testGetSortScope_univ_includingBuiltins() {
        // should be the sum of all *non-builtin* sig scopes
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sig sig3 = new Sig.PrimSig("S3");
        when(scoper.sig2scope(sig1)).thenReturn(3);
        when(scoper.sig2scope(sig2)).thenReturn(7);
        when(scoper.sig2scope(sig3)).thenReturn(11);
        SortPolicy policy = new UnivSortPolicy(
                univ, Arrays.asList(sig1, sig2, sig3, Sig.UNIV, Sig.SIGINT, Sig.STRING), scoper);
        assertEquals(21, policy.getSortScope(univ));
    }

    @Test
    public void testGetSortScope_int() {
        // should be the bitwidth
        when(scoper.getBitwidth()).thenReturn(7);
        SortPolicy policy = new UnivSortPolicy(univ, new ArrayList<>(), scoper);
        assertEquals(7, policy.getSortScope(Sort.Int()));
    }

}
