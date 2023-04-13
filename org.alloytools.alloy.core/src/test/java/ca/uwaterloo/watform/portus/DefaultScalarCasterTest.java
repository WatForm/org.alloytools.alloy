package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import org.junit.Before;
import org.junit.Test;

import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class DefaultScalarCasterTest {

    private ScalarCaster scalarCaster;
    private ScalarCaster mockRoot;

    private Translator mockTranslator;
    private SortPolicy mockSortPolicy;
    private RangeAssigner mockRangeAssigner;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(ScalarCaster.class);
        mockTranslator = mock(Translator.class);
        mockSortPolicy = mock(SortPolicy.class);
        mockRangeAssigner = mock(RangeAssigner.class);
        context = new TranslationContext(
                new PortusOptions(), mock(ScopeComputer.class), mockSortPolicy, mockRangeAssigner);
        scalarCaster = new DefaultScalarCaster(mockTranslator, mockRoot);
    }

    @Test
    public void testCastToScalar_integer() {
        // test castToScalar(2) = (2: Int, Top)
        Term flagTwo = Term.mkVar("flagTwo");
        when(mockTranslator.translate(argThat(isSameAs(ExprConstant.makeNUMBER(2))), any())).thenReturn(flagTwo);

        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(ExprConstant.makeNUMBER(2), context);
        assertNotNull(result);
        assertEquals(flagTwo, result.a.getTerm());
        assertEquals(Sort.Int(), result.a.getSort());
        assertTrue(result.a.getFreeVars().isEmpty());
        assertEquals(Term.mkTop(), result.b);
    }

    @Test
    public void testCastToScalar_integerWithNoopWrappers() {
        // like the above, but wrap 2 and 3 in a variety of noop, cast2int, cast2sigint
        Term flagTwo = Term.mkVar("flagTwo");
        when(mockTranslator.translate(argThat(isSameAs(ExprConstant.makeNUMBER(2))), any())).thenReturn(flagTwo);

        Expr expr = ExprUnary.Op.NOOP.make(null, ExprConstant.makeNUMBER(2).cast2int().cast2sigint().cast2int());
        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(expr, context);
        assertNotNull(result);
        assertEquals(flagTwo, result.a.getTerm());
        assertEquals(Sort.Int(), result.a.getSort());
        assertTrue(result.a.getFreeVars().isEmpty());
        assertEquals(Term.mkTop(), result.b);
    }

    @Test
    public void testCastToScalar_oneSig() {
        // test castToScalar(A) = (@2: sortA, Top) when A is a one sig and @1 is its one domain element
        Sig sigA = new Sig.PrimSig("A", Attr.ONE);
        Sort sortA = Sort.mkSortConst("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any())).thenReturn(new Pair<>(2, 2));

        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(sigA, context);
        assertNotNull(result);
        assertEquals(Term.mkDomainElement(2, sortA), result.a.getTerm());
        assertEquals(sortA, result.a.getSort());
        assertTrue(result.a.getFreeVars().isEmpty());
        assertEquals(Term.mkTop(), result.b);
    }

    @Test
    public void testCastToScalar_boundVar() {
        // test castToScalar(x) = (t: sort, Top) when x is a bound variable mapped to t
        Sort sort = Sort.mkSortConst("Sort");
        AnnotatedTerm mapped = new AnnotatedTerm(Term.mkVar("t").of(sort));
        context.addTermMapping("x", mapped);

        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(ExprVar.make(null, "x"), context);
        assertNotNull(result);
        assertEquals(mapped, result.a);
        assertEquals(Term.mkTop(), result.b);
    }

    @Test
    public void testCastToScalar_letVar() {
        // test castToScalar(x) recurses to x's let mapping when x has one
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar mapping = ExprVar.make(null, "mapping");
        AnnotatedTerm flag = new AnnotatedTerm(Term.mkVar("flag").of(sort));
        Term flagGuard = Term.mkVar("flagGuard");
        when(mockRoot.castToScalar(eq(mapping), any()))
                .thenReturn(new Pair<>(flag, flagGuard));
        context.addLetMapping("x", mapping);

        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(ExprVar.make(null, "x"), context);
        assertNotNull(result);
        assertEquals(flag, result.a);
        assertEquals(flagGuard, result.b);
    }

}
