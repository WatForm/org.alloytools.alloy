package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;

import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class JoinOptTranslatorTest {

    private final Sort testSort = Sort.mkSortConst("testSort");

    private JoinOptTranslator translator;
    private Translator mockRoot;
    private ScalarCaster mockScalarCaster;

    private SortPolicy mockSortPolicy;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockScalarCaster = mock(ScalarCaster.class);
        translator = new JoinOptTranslator(mockRoot, mockScalarCaster);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(testSort));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(new ArrayList<>(), mockSortPolicy, mockScoper));
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_nonJoin() {
        // test that translating some random binary expression doesn't do anything
        assertNull(translator.translate(ExprConstant.TRUE.and(ExprConstant.FALSE), context));
    }

    @Test
    public void testTranslate_join_inapplicable() {
        // test that [[x \in e1 . e2]] doesn't get optimized when neither are variables
        ExprVar a = ExprVar.make(null, "a");
        ExprVar b = ExprVar.make(null, "b");
        assertNull(translator.translate(a.product(b).join(a.product(b)), context));
    }

    @Test
    public void testTranslate_join_left_nilary() {
        // test [[x \in v . e]] := guard && [[(v,x) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(alloyV)), any()))
                .thenReturn(new Scalar(new AnnotatedTerm(v), guard));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(v, x), e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprElementOf.make(TermTuple.fromVars(x), alloyV.join(e)), context);
        Term expected = Term.mkAnd(guard, flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_left_unary_oneTuple() {
        // test [[x \in f . e]] := guard(x) && [[f(x) \in e]] when f is a unary scalar function
        ExprVar e = ExprVar.make(null, "e");
        ExprVar f = ExprVar.make(null, "f");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(f)), any())).thenReturn(new Scalar(1, testSort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Var x = Term.mkVar("x");
        Var flag = Term.mkVar("flag");
        TermTuple expectedTuple = new TermTuple(new AnnotatedTerm(Term.mkApp("f", x), testSort));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(expectedTuple, e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprElementOf.make(TermTuple.fromVars(x.of(testSort)), f.join(e)), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x), flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_left_unary_twoTuple() {
        // test [[(x,y) \in f . e]] := guard(x) && [[(f(x),y) \in e]] when f is a unary scalar function
        ExprVar e = ExprVar.make(null, "e");
        ExprVar f = ExprVar.make(null, "f");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(f)), any())).thenReturn(new Scalar(1, testSort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Var x = Term.mkVar("x");
        AnnotatedVar y = Term.mkVar("y").of(testSort);
        Var flag = Term.mkVar("flag");
        TermTuple expectedTuple = new TermTuple(new AnnotatedTerm(Term.mkApp("f", x), testSort), new AnnotatedTerm(y));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(expectedTuple, e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(testSort), y), f.join(e)), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x), flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_left_binary_twoTuple() {
        // test [[(x,y) \in f . e]] := guard(x,y) && [[f(x,y) \in e]] when f is a binary scalar function
        ExprVar e = ExprVar.make(null, "e");
        ExprVar f = ExprVar.make(null, "f");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(f)), any())).thenReturn(new Scalar(2, testSort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var flag = Term.mkVar("flag");
        TermTuple expectedTuple = new TermTuple(new AnnotatedTerm(Term.mkApp("f", x, y), testSort));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(expectedTuple, e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(testSort), y.of(testSort)), f.join(e)), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x, y), flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_left_binary_threeTuple() {
        // test [[(x,y,z) \in f . e]] := guard(x,y) && [[(f(x,y),z) \in e]] when f is a binary scalar function
        ExprVar e = ExprVar.make(null, "e");
        ExprVar f = ExprVar.make(null, "f");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(f)), any())).thenReturn(new Scalar(2, testSort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        AnnotatedVar z = Term.mkVar("z").of(testSort);
        Var flag = Term.mkVar("flag");
        TermTuple expectedTuple = new TermTuple(
                new AnnotatedTerm(Term.mkApp("f", x, y), testSort), new AnnotatedTerm(z));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(expectedTuple, e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(testSort), y.of(testSort), z), f.join(e)), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x, y), flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_right() {
        // test [[x \in e . v]] := guard && [[(x,v) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(alloyV)), any()))
                .thenReturn(new Scalar(new AnnotatedTerm(v), guard));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x, v), e))), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprElementOf.make(TermTuple.fromVars(x), e.join(alloyV)), context);
        Term expected = Term.mkAnd(guard, flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_join_composition() {
        // test castToScalar(x.f) implements composition
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyF = ExprVar.make(null, "f");
        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var guardX = Term.mkVar("guardX");
        when(mockScalarCaster.castToScalar(argThat(isSameAs(alloyX)), any()))
                .thenReturn(new Scalar(new AnnotatedTerm(x), guardX));
        when(mockScalarCaster.castToScalar(argThat(isSameAs(alloyF)), any()))
                .thenReturn(new Scalar(1, testSort,
                        tuple -> Term.mkApp("f", tuple.getTerms()),
                        tuple -> Term.mkApp("guardF", tuple.getTerms())));

        Scalar scalar = translator.castToScalar(alloyX.join(alloyF), context);
        assertNotNull(scalar);
        assertTrue(scalar.isNilary());
        assertEquals(Term.mkApp("f", x.variable()), scalar.getNilaryScalar());
        assertEquals(Term.mkAnd(guardX, Term.mkApp("guardF", x.variable())), scalar.getNilaryGuard());
    }

}
