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

import static org.junit.Assert.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class SimpleScalarOptTranslatorTest {

    private Translator mockRoot;
    private ScalarCaster mockScalarCaster;

    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockScalarCaster = mock(ScalarCaster.class);
        SortPolicy mockSortPolicy = mock(SortPolicy.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
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
        Term guardX = Term.mkVar("guardX");
        Term guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sort)), guardY));

        Translator translator = new SimpleScalarOptTranslator(mockRoot, mockScalarCaster);
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
        Term guardX = Term.mkVar("guardX");
        Term guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sort)), guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sort)), guardY));

        Translator translator = new SimpleScalarOptTranslator(mockRoot, mockScalarCaster);
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
        Term guardX = Term.mkVar("guardX");
        Term guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sortX)), guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sortY)), guardY));

        Translator translator = new SimpleScalarOptTranslator(mockRoot, mockScalarCaster);
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
        Term guardX = Term.mkVar("guardX");
        Term guardY = Term.mkVar("guardY");
        when(mockScalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(sortX)), guardX));
        when(mockScalarCaster.castToScalar(eq(alloyY), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(y.of(sortY)), guardY));

        Translator translator = new SimpleScalarOptTranslator(mockRoot, mockScalarCaster);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.in(alloyY), context);
        assertEquals(Term.mkBottom(), result);
    }

}
