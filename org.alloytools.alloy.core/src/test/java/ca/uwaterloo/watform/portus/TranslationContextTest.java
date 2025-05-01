package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.withSettings;

public class TranslationContextTest {

    private TranslationContext context;

    @Before
    public void setUp() {
        ScopeComputer scoper = mock(ScopeComputer.class);
        SortPolicy sortPolicy = mock(SortPolicy.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(mock(ModelInfo.class), new ArrayList<>(), sortPolicy, scoper));
        context = new TranslationContext(new PortusOptions(), scoper, sortPolicy, mockRangeAssigner);
    }

    @Test
    public void testLetMappingContextRestoration() {
        Expr x = ExprVar.make(null, "x");
        Expr y = ExprVar.make(null, "y");
        context.addLetMapping("x", x);
        context.addLetMapping("y", y);
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        VarMappingContext.LetContext letContext = context.getLetMapping("x");
        assertNotNull(letContext);
        assertEquals(x, letContext.getExpr());

        letContext.useLetMapping(context);
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        letContext.resetMapping();
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        letContext = context.getLetMapping("y");
        assertNotNull(letContext);
        assertEquals(y, letContext.getExpr());

        letContext.useLetMapping(context);
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        letContext.resetMapping();
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));
    }

    @Test
    public void testLetMappingWithCopying() {
        // Test that when we copy a context containing let mappings, the copied context's let mappings affect
        // the new context, not the old context.
        ExprVar x = ExprVar.make(null, "x");
        context.addLetMapping("x", x);
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasTermMapping("x"));

        TranslationContext contextCopy = new TranslationContext(context);
        assertTrue(contextCopy.hasLetMapping("x"));
        assertFalse(contextCopy.hasTermMapping("x"));

        VarMappingContext.LetContext copyLetContext = contextCopy.getLetMapping("x");
        assertNotNull(copyLetContext);
        assertEquals(x, copyLetContext.getExpr());

        copyLetContext.useLetMapping(contextCopy);
        assertFalse(contextCopy.hasLetMapping("x")); // affects copy
        assertFalse(contextCopy.hasTermMapping("x"));
        assertTrue(context.hasLetMapping("x")); // doesn't affect original
        assertFalse(context.hasTermMapping("x"));

        copyLetContext.resetMapping();
        assertTrue(contextCopy.hasLetMapping("x"));
        assertFalse(contextCopy.hasTermMapping("x"));
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testSimultaneousLetMapping() {
        // Test that when we simultaneously add two let mappings, they don't interfere.
        Sort sort = Sort.mkSortConst("S");
        AnnotatedVar xVar = Term.mkVar("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(xVar));

        ExprVar a = ExprVar.make(null, "a");
        ExprVar x = ExprVar.make(null, "x");
        List<Pair<String, Expr>> varNamesAndBoundExprs = Arrays.asList(
                new Pair<>("x", a),
                new Pair<>("y", x));
        context.addSimultaneousLetMappings(varNamesAndBoundExprs);

        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        // y should be mapped to the original x and not a
        // that is, there should be no let mapping for x within y's let mapping
        VarMappingContext.LetContext letContext = context.getLetMapping("y");
        assertNotNull(letContext);
        letContext.useLetMapping(context);
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertTrue(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));

        letContext.resetMapping();
        context.removeMapping("x");
        context.removeMapping("y");

        // removed the mappings - back to what it was before (which is the same as y's let context)
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertTrue(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));
    }

}