package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.IntegerLiteral;
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

public class IntAsScalarTranslatorTest {

    private ScalarCaster mockScalarCaster;

    private TranslationContext context;

    @Before
    public void setUp() {
        mockScalarCaster = mock(ScalarCaster.class);
        SortPolicy mockSortPolicy = mock(SortPolicy.class);
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(mock(ModelInfo.class), new ArrayList<>(), mockSortPolicy, mockScoper));
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_intExprAsScalar() {
        // test [[i]] := guard => i else 0 when castToScalar(i) = (i, guard)
        ExprVar alloyI = ExprVar.make(null, "i");
        Var i = Term.mkVar("i");
        Var guard = Term.mkVar("guard");
        when(mockScalarCaster.castToScalar(eq(alloyI), any())).thenReturn(new Scalar(Sort.Int(), i, guard));

        Translator translator = new IntAsScalarTranslator(mockScalarCaster);
        Term result = translator.translate(alloyI, context);
        Term expected = Term.mkIfThenElse(guard, i, IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

}
