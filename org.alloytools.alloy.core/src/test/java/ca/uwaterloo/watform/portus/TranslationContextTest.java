package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;

public class TranslationContextTest {

    private TranslationContext context;

    @Before
    public void setUp() {
        ScopeComputer scoper = mock(ScopeComputer.class);
        SortPolicy sortPolicy = mock(SortPolicy.class);
        context = new TranslationContext(new FortressOptions(), scoper, sortPolicy);
    }

    @Test
    public void testLetMappingContextRestoration() {
        Expr x = ExprVar.make(null, "x");
        Expr y = ExprVar.make(null, "y");
        context.addLetMapping("x", x);
        context.addLetMapping("y", y);
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));

        TranslationContext.LetContext letContext = context.getLetMapping("x");
        assertNotNull(letContext);
        assertEquals(x, letContext.getExpr());

        letContext.useLetMapping(context);
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));

        letContext.resetMapping();
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));

        letContext = context.getLetMapping("y");
        assertNotNull(letContext);
        assertEquals(y, letContext.getExpr());

        letContext.useLetMapping(context);
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));

        letContext.resetMapping();
        assertTrue(context.hasLetMapping("x"));
        assertTrue(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testLetMappingWithCopying() {
        // Test that when we copy a context containing let mappings, the copied context's let mappings affect
        // the new context, not the old context.
        ExprVar x = ExprVar.make(null, "x");
        context.addLetMapping("x", x);
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasVarMapping("x"));

        TranslationContext contextCopy = new TranslationContext(context);
        assertTrue(contextCopy.hasLetMapping("x"));
        assertFalse(contextCopy.hasVarMapping("x"));

        TranslationContext.LetContext copyLetContext = contextCopy.getLetMapping("x");
        assertNotNull(copyLetContext);
        assertEquals(x, copyLetContext.getExpr());

        copyLetContext.useLetMapping(contextCopy);
        assertFalse(contextCopy.hasLetMapping("x")); // affects copy
        assertFalse(contextCopy.hasVarMapping("x"));
        assertTrue(context.hasLetMapping("x")); // doesn't affect original
        assertFalse(context.hasVarMapping("x"));

        copyLetContext.resetMapping();
        assertTrue(contextCopy.hasLetMapping("x"));
        assertFalse(contextCopy.hasVarMapping("x"));
        assertTrue(context.hasLetMapping("x"));
        assertFalse(context.hasVarMapping("x"));
    }

}