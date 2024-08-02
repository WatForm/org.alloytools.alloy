package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

public class OneSigOptTranslatorTest {

    private final Sort testSort = Sort.mkSortConst("Sort");
    private final Sig.PrimSig testOneSig = new Sig.PrimSig("Sig", Attr.ONE);

    private Translator mockTranslator;
    private SortPolicy mockSortPolicy;
    private SigAxioms mockSigAxioms;
    private RangeAssigner mockRangeAssigner;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockTranslator = mock(Translator.class);
        mockSortPolicy = mock(SortPolicy.class);
        mockSigAxioms = mock(SigAxioms.class);
        mockRangeAssigner = mock(RangeAssigner.class);
        ScopeComputer mockScopeComputer = mock(ScopeComputer.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(testSort));
        context = new TranslationContext(
                new PortusOptions(), mockScopeComputer, mockSortPolicy, mockRangeAssigner);

        when(mockSortPolicy.getSort(testOneSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(3);
        when(mockScopeComputer.sig2scope(testOneSig)).thenReturn(1);
        when(mockScopeComputer.isExact(testOneSig)).thenReturn(true);
    }

    @Test
    public void testTranslate() {
        // test translating a one sig adds the range axiom
        OneSigOptTranslator opt = new OneSigOptTranslator(mockTranslator, mockSortPolicy, mockSigAxioms);
        Term result = opt.translate(testOneSig, context);
        assertNotNull(result);
        verify(mockRangeAssigner, atLeastOnce()).addRangeAxiom(eq(testOneSig), any(), any());
    }

    @Test
    public void testTranslate_withChild() {
        // test that a child of a one sig is supported
        OneSigOptTranslator opt = new OneSigOptTranslator(mockTranslator, mockSortPolicy, mockSigAxioms);
        Sig child = new Sig.PrimSig(null, "child", new Pos("foo.als", 1, 2), testOneSig);
        Term result = opt.translate(testOneSig, context);
        assertNotNull(result);
        verify(mockRangeAssigner, atLeastOnce()).addRangeAxiom(eq(testOneSig), any(), any());
        verify(mockSigAxioms, atLeastOnce()).addPrimSigChildrenAxioms(eq(testOneSig), any());
        verify(mockTranslator, atLeastOnce()).translate(eq(child), any());
    }

    @Test
    public void testTranslate_childOfOrderedSig() {
        // test that we *don't* optimize a one sig that is a child of an ordered sig
        OneSigOptTranslator opt = new OneSigOptTranslator(mockTranslator, mockSortPolicy, mockSigAxioms);
        Sig.PrimSig parent = new Sig.PrimSig("parent");
        context.setSigOrdered(parent);
        Sig child = new Sig.PrimSig(null, "child", new Pos("foo.als", 1, 2), parent, Attr.ONE);
        Term result = opt.translate(child, context);
        assertNull(result);
    }

    @Test
    public void testCastToScalar() {
        // test castToScalar(A) = (@1: sortA, Top) when A is a one sig and @1 is its one domain element
        OneSigOptTranslator opt = new OneSigOptTranslator(mockTranslator, mockSortPolicy, mockSigAxioms);

        Term flagRangeAxiom = Term.mkVar("rangeAxiom");
        when(mockTranslator.translate(any(), any())).thenReturn(flagRangeAxiom);
        when(mockRangeAssigner.getDomainElementRange(testOneSig)).thenReturn(new Pair<>(1, 1));

        Scalar result = opt.castToScalar(testOneSig, context);
        assertNotNull(result);
        assertTrue(result.isNilary());
        assertEquals(Term.mkDomainElement(1, testSort), result.getNilaryScalar());
        assertEquals(testSort, result.getResultSort());
        assertEquals(Term.mkTop(), result.getNilaryGuard());
    }

}
