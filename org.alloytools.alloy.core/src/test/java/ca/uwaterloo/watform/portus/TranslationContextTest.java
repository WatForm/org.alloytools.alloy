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

        letContext.useLetMapping();
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

        letContext.useLetMapping();
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

}