package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.Objects;

import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class DefaultScalarCasterTest {

    private final Sort testSort = Sort.mkSortConst("Sort");
    private final Sig testOneSig = new Sig.PrimSig("Sig", Attr.ONE);

    private ScalarCaster scalarCaster;
    private ScalarCaster mockRoot;

    private Translator mockTranslator;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(ScalarCaster.class);
        mockTranslator = mock(Translator.class);
        ScopeComputer mockScopeComputer = mock(ScopeComputer.class);
        SortPolicy mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(testSort));
        // Use the constructor so the range assigner can be copied without issue
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings()
                .useConstructor(Collections.singleton(testOneSig)));
        context = new TranslationContext(
                new PortusOptions(), mockScopeComputer, mockSortPolicy, mockRangeAssigner);
        scalarCaster = new DefaultScalarCaster(mockTranslator, mockRoot, mockSortPolicy);

        when(mockSortPolicy.getSort(testOneSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(3);
        when(mockScopeComputer.sig2scope(testOneSig)).thenReturn(1);
        when(mockScopeComputer.isExact(testOneSig)).thenReturn(true);
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
        when(mockRoot.castToScalar(any(), any()))
                .then(args -> scalarCaster.castToScalar(args.getArgument(0), args.getArgument(1)));

        Expr expr = ExprUnary.Op.NOOP.make(null, ExprConstant.makeNUMBER(2).cast2int().cast2sigint().cast2int());
        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(expr, context);
        assertNotNull(result);
        assertEquals(flagTwo, result.a.getTerm());
        assertEquals(Sort.Int(), result.a.getSort());
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
        when(mockRoot.castToScalar(eq(mapping), any())).thenReturn(new Pair<>(flag, flagGuard));
        context.addLetMapping("x", mapping);

        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(ExprVar.make(null, "x"), context);
        assertNotNull(result);
        assertEquals(flag, result.a);
        assertEquals(flagGuard, result.b);
    }

    @Test
    public void testCastToScalar_call() {
        // test castToScalar(f[x]) recurses to the definition of f, mapping arguments
        Expr funcBody = ExprVar.make(null, "body");
        Func func = new Func(null, null, "f", Collections.singletonList(testOneSig.oneOf("y")), testOneSig, funcBody);

        ExprVar x = ExprVar.make(null, "x");
        Pair<AnnotatedTerm, Term> flag = new Pair<>(
                new AnnotatedTerm(Term.mkVar("flag").of(testSort)), Term.mkVar("flagGuard"));
        when(mockRoot.castToScalar(eq(funcBody), any())).then(args -> {
           // make sure y is mapped to x
           TranslationContext newContext = args.getArgument(1); 
           assertTrue(newContext.hasLetMapping("y"));
           assertEquals(x, Objects.requireNonNull(newContext.getLetMapping("y")).getExpr());
           return flag;
        });

        Expr call = ExprCall.make(null, null, func, Collections.singletonList(x), 0);
        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(call, context);
        assertEquals(flag, result);
    }

    @Test
    public void testCastToScalar_ite() {
        // test castToScalar(c => left else right) = (c => left else right, c => leftGuard else rightGuard)
        Expr cond = ExprVar.make(null, "cond");
        Expr left = ExprVar.make(null, "left");
        Expr right = ExprVar.make(null, "right");
        Term condTerm = Term.mkVar("cond");
        Var leftTerm = Term.mkVar("left");
        Var rightTerm = Term.mkVar("right");
        Term leftGuard = Term.mkVar("leftGuard");
        Term rightGuard = Term.mkVar("rightGuard");
        when(mockTranslator.translate(eq(cond), any())).thenReturn(condTerm);
        when(mockRoot.castToScalar(eq(left), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(leftTerm.of(testSort)), leftGuard));
        when(mockRoot.castToScalar(eq(right), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(rightTerm.of(testSort)), rightGuard));

        Expr ite = ExprITE.make(null, cond, left, right);
        Pair<AnnotatedTerm, Term> result = scalarCaster.castToScalar(ite, context);
        assertNotNull(result);

        Term expectedScalar = Term.mkIfThenElse(condTerm, leftTerm, rightTerm);
        Term expectedGuard = Term.mkIfThenElse(condTerm, leftGuard, rightGuard);
        assertEquals(expectedScalar, result.a.getTerm());
        assertEquals(testSort, result.a.getSort());
        assertEquals(expectedGuard, result.b);
    }

}
