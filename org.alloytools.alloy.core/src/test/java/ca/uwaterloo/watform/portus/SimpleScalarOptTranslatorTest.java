package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;

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

    private TranslationContext context;

    @Before
    public void setUp() {
        mockTranslator = mock(Translator.class);
        mockScalarCaster = mock(ScalarCaster.class);
        SortPolicy mockSortPolicy = mock(SortPolicy.class);
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(new ArrayList<>(), mockSortPolicy, mockScoper));
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
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(guardX.of(Sort.Bool()))));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sort)), new AnnotatedTerm(guardY.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);

        Term expected = Term.mkIfThenElse(guardX,
                Term.mkAnd(guardY, Term.mkEq(x, y)),
                Term.mkNot(guardY));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarIn() {
        // test [[x in y]] := guardX => (guardY && x = y)
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardX = Term.mkVar("guardX");
        Var guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(guardX.of(Sort.Bool()))));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sort)), new AnnotatedTerm(guardY.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.in(alloyY), context);

        Term expected = Term.mkImp(guardX, Term.mkAnd(guardY, Term.mkEq(x, y)));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_scalarEquals_shortCircuit() {
        // test [[x = y]] := false when x and y are of different sorts
        Sort sortX = Sort.mkSortConst("SortX");
        Sort sortY = Sort.mkSortConst("SortY");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardX = Term.mkVar("guardX");
        Var guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sortX)), new AnnotatedTerm(guardX.of(Sort.Bool()))));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sortY)), new AnnotatedTerm(guardY.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);
        assertEquals(Term.mkBottom(), result);
    }

    @Test
    public void testTranslate_scalarIn_shortCircuit() {
        // test [[x in y]] := false when x and y are of different sorts
        Sort sortX = Sort.mkSortConst("SortX");
        Sort sortY = Sort.mkSortConst("SortY");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardX = Term.mkVar("guardX");
        Var guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sortX)), new AnnotatedTerm(guardX.of(Sort.Bool()))));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sortY)), new AnnotatedTerm(guardY.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.in(alloyY), context);
        assertEquals(Term.mkBottom(), result);
    }

    @Test
    public void testTranslate_scalarInNonScalar() {
        // test [[v in e]] := guard => [[v \in e]]
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var x = Term.mkVar("x");
        Var guardX = Term.mkVar("guardX");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(guardX.of(Sort.Bool()))));

        Var flag = Term.mkVar("flag");
        when(mockTranslator.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(sort), alloyE))), any()))
                .thenReturn(flag);

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        Term result = translator.translate(alloyX.in(alloyE), context);
        Term expected = Term.mkImp(guardX, flag);
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
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(guardX.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        Term result = translator.translate(alloyX.equal(alloyE), context);
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
        when(mockScalarCaster.castToScalar(eq(alloyE), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(e.of(sort)), new AnnotatedTerm(guard.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
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

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        Term result = translator.translate(ExprElementOf.make(v.of(sort), alloyE), context);
        assertNull(result);
    }

    @Test
    public void testTranslate_scalarElementOf_notUnary() {
        // test [[(v1,v2) \in e]] returns null
        Sort sort = Sort.mkSortConst("Sort");
        ExprVar alloyE = ExprVar.make(null, "e");
        Var e = Term.mkVar("e");
        Var v1 = Term.mkVar("v1");
        Var v2 = Term.mkVar("v2");
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(eq(alloyE), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(e.of(sort)), new AnnotatedTerm(guard.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(v1.of(sort), v2.of(sort)), alloyE), context);
        assertNull(result);
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
        when(mockScalarCaster.castToScalar(eq(alloyE), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(e.of(sortE)), new AnnotatedTerm(guard.of(Sort.Bool()))));

        Translator translator = new SimpleScalarOptTranslator(mockTranslator, mockScalarCaster);
        Term result = translator.translate(ExprElementOf.make(v.of(sortV), alloyE), context);
        assertEquals(Term.mkBottom(), result);
    }

}
