package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

import static ca.uwaterloo.watform.portus.AlloyASTMatcher.isAlphaEquivalent;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class SimpleScalarOptTranslatorTest {

    private Translator mockTranslator;
    private ScalarCaster mockScalarCaster;
    private NameGenerator nameGenerator;

    private TranslationContext context;

    @Before
    public void setUp() {
        mockTranslator = mock(Translator.class);
        mockScalarCaster = mock(ScalarCaster.class);
        nameGenerator = new SanitizingNameGenerator();
        SortPolicy mockSortPolicy = mock(SortPolicy.class);
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(mock(ModelInfo.class), new ArrayList<>(), mockSortPolicy, mockScoper));
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_scalarEquals() {
        // test [[x = y]] := guardX => (guardY && x = y) else !guardY
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardX = Term.mkVar("guardX");
        Var guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any())).thenReturn(new Scalar(sort, x, guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any())).thenReturn(new Scalar(sort, y, guardY));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);

        Term expected = Term.mkIfThenElse(guardX,
                Term.mkAnd(guardY, Term.mkEq(x, y)),
                Term.mkNot(guardY));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarIn() {
        // test [[v in e]] := guard => [[v \in e]]
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var x = Term.mkVar("x");
        Var guardX = Term.mkVar("guardX");
        when(mockScalarCaster.castToScalar(eq(alloyX), any())).thenReturn(new Scalar(sort, x, guardX));

        Var flag = Term.mkVar("flag");
        when(mockTranslator.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(sort), alloyE))), any()))
                .thenReturn(flag);

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(alloyX.in(alloyE), context);
        Term expected = Term.mkImp(guardX, flag);
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarIn_arity1() {
        // test [[f in e]] := forall x: S . guard(x) => [[(x,f(x)) \in e]] when f is a unary scalar function
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyF = ExprVar.make(null, "f");
        ExprVar alloyE = ExprVar.make(null, "e");
        when(mockScalarCaster.castToScalar(eq(alloyF), any())).thenReturn(new Scalar(
                Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Var x = Term.mkVar("x0_0");
        Var flag = Term.mkVar("flag");
        when(mockTranslator.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(new TermTuple(
                        new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(Term.mkApp("f", x), sort)), alloyE))), any()))
                .thenReturn(flag);

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(alloyF.in(alloyE), context);
        Term expected = Term.mkForall(x.of(sort), Term.mkImp(Term.mkApp("guard", x), flag));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarEq_arity1() {
        // test [[f = g]] := forall x: S . guardF(x) => guardG(x) && f(x) = g(x) else !guardG(x)
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyF = ExprVar.make(null, "f");
        ExprVar alloyG = ExprVar.make(null, "g");
        when(mockScalarCaster.castToScalar(eq(alloyF), any())).thenReturn(new Scalar(
                Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guardF", tuple.getTerms())));
        when(mockScalarCaster.castToScalar(eq(alloyG), any())).thenReturn(new Scalar(
                Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("g", tuple.getTerms()),
                tuple -> Term.mkApp("guardG", tuple.getTerms())));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(alloyF.equal(alloyG), context);

        Var x = Term.mkVar("x0_0");
        Term expected = Term.mkForall(x.of(sort), Term.mkIfThenElse(Term.mkApp("guardF", x),
                Term.mkAnd(Term.mkApp("guardG", x), Term.mkEq(Term.mkApp("f", x), Term.mkApp("g", x))),
                Term.mkNot(Term.mkApp("guardG", x))));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarEqualsNonScalar_doesntApply() {
        // test that the optimization tested above doesn't apply to [[v = e]]
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var x = Term.mkVar("x");
        Var guardX = Term.mkVar("guardX");
        when(mockScalarCaster.castToScalar(eq(alloyX), any())).thenReturn(new Scalar(sort, x, guardX));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(alloyX.equal(alloyE), context);
        assertNull(result);
    }

    @Test
    public void testTranslate_scalarEquals_mismatchedSorts_doesntApply() {
        // test [[x = y]] doesn't apply when x and y are mismatched sorts
        Sort sortX = Sort.mkSortConst("SortX");
        Sort sortY = Sort.mkSortConst("SortY");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardX = Term.mkVar("guardX");
        Var guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any())).thenReturn(new Scalar(sortX, x, guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any())).thenReturn(new Scalar(sortY, y, guardY));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);
        assertNull(result);
    }

    @Test
    public void testTranslate_scalarElementOf() {
        // test [[v \in e]] := guard && v = e
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var e = Term.mkVar("e");
        Var v = Term.mkVar("v");
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(eq(alloyE), any())).thenReturn(new Scalar(sort, e, guard));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(v.of(sort), alloyE), context);

        Term expected = Term.mkAnd(guard, Term.mkEq(v, e));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarElementOf_notScalar() {
        // test [[v \in e]] returns null when e isn't a scalar
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var v = Term.mkVar("v");
        when(mockScalarCaster.castToScalar(eq(alloyE), any())).thenReturn(null);

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(v.of(sort), alloyE), context);
        assertNull(result);
    }

    @Test
    public void testTranslate_scalarElementOf_arityMismatch() {
        // test [[(v1,v2) \in e]] returns null when e is a nilary scalar
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var e = Term.mkVar("e");
        Var v1 = Term.mkVar("v1");
        Var v2 = Term.mkVar("v2");
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(eq(alloyE), any())).thenReturn(new Scalar(sort, e, guard));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(v1.of(sort), v2.of(sort)), alloyE), context);
        assertNull(result);
    }

    @Test
    public void testTranslate_scalarElementOf_unary() {
        // test [[(x,y) \in f]] := guard(x) && y = f(x) when f is a unary scalar
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar f = ExprVar.make(null, "f");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        when(mockScalarCaster.castToScalar(eq(f), any())).thenReturn(new Scalar(Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(sort), y.of(sort)), f), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x), Term.mkEq(y, Term.mkApp("f", x)));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarElementOf_binary() {
        // test [[(x,y,z) \in f]] := guard(x,y) && z = f(x,y) when f is a binary scalar
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar f = ExprVar.make(null, "f");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var z = Term.mkVar("z");
        when(mockScalarCaster.castToScalar(eq(f), any())).thenReturn(new Scalar(Arrays.asList(sort, sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerms()),
                tuple -> Term.mkApp("guard", tuple.getTerms())));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(sort), y.of(sort), z.of(sort)), f), context);
        Term expected = Term.mkAnd(Term.mkApp("guard", x, y), Term.mkEq(z, Term.mkApp("f", x, y)));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarElementOf_shortCircuit() {
        // test [[v \in e]] := false when v and e are of different sorts
        Sort sortE = Sort.mkSortConst("SortE");
        Sort sortV = Sort.mkSortConst("SortV");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var e = Term.mkVar("e");
        Var v = Term.mkVar("v");
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(eq(alloyE), any())).thenReturn(new Scalar(sortE, e, guard));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster, nameGenerator);
        Term result = translator.translate(ExprElementOf.make(v.of(sortV), alloyE), context);
        assertEquals(Term.mkBottom(), result);
    }

}
