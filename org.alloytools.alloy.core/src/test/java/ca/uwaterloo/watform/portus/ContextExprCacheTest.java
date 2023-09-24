package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.mock;

public class ContextExprCacheTest {

    private SortPolicy sortPolicy;

    @Before
    public void setUp() {
        sortPolicy = mock(SortPolicy.class);
    }

    private ExprVar makeTestVar(String label) {
        return ExprVar.make(null, label);
    }

    @Test
    public void testContextExprCache_basic() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context = new VarMappingContext();
        Expr someExpr = ExprConstant.ONE;

        cache.put(someExpr, context, 1);
        assertEquals(Integer.valueOf(1), cache.get(someExpr, context));
    }

    @Test
    public void testContextExprCache_compoundExpr() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context = new VarMappingContext();
        Expr someExpr = ExprConstant.ONE.iplus(ExprConstant.ONE);

        cache.put(someExpr, context, 1);
        assertEquals(Integer.valueOf(1), cache.get(someExpr, context));
    }

    @Test
    public void testContextExprCache_multipleSameContext() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context = new VarMappingContext();
        Expr expr1 = ExprConstant.ONE.iplus(ExprConstant.ONE);
        Expr expr2 = ExprConstant.IDEN.product(ExprConstant.EMPTYNESS);

        cache.put(expr1, context, 1);
        cache.put(expr2, context, 2);
        assertEquals(Integer.valueOf(1), cache.get(expr1, context));
        assertEquals(Integer.valueOf(2), cache.get(expr2, context));
    }

    @Test
    public void testContextExprCache_twoDifferentContexts_letMapping() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();

        ExprVar x = makeTestVar("x");
        context1.addLetMapping("x", ExprConstant.ZERO);
        context2.addLetMapping("x", ExprConstant.ONE);

        // They remain distinct because they expand to different things.
        cache.put(x, context1, 1);
        cache.put(x, context2, 2);
        assertEquals(Integer.valueOf(1), cache.get(x, context1));
        assertEquals(Integer.valueOf(2), cache.get(x, context2));
    }

    @Test
    public void testContextExprCache_twoDifferentContexts_termMapping() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();

        ExprVar alloyX = makeTestVar("x");
        Sort sort = Sort.mkSortConst("Sort");
        AnnotatedVar x = Term.mkVar("x").of(sort);
        AnnotatedVar y = Term.mkVar("y").of(sort);

        context1.addTermMapping("x", new AnnotatedTerm(x));
        context2.addTermMapping("x", new AnnotatedTerm(y));

        // They remain distinct because they expand to different things, even
        // with term mappings.
        cache.put(alloyX, context1, 1);
        cache.put(alloyX, context2, 2);
        assertEquals(Integer.valueOf(1), cache.get(alloyX, context1));
        assertEquals(Integer.valueOf(2), cache.get(alloyX, context2));
    }

    @Test
    public void testContextExprCache_differentContextsMapToSameThing() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();

        ExprVar x = makeTestVar("x");
        context2.addLetMapping("x", ExprConstant.ZERO);

        // They should not remain distinct because they expand to the same thing.
        cache.put(ExprConstant.ZERO, context1, 1);
        cache.put(x, context2, 2);
        assertEquals(Integer.valueOf(2), cache.get(ExprConstant.ZERO, context1));
        assertEquals(Integer.valueOf(2), cache.get(x, context2));
    }

    @Test
    public void testContextExprCache_termMappingsToSameThing() {
        ContextExprCache<Integer> cache = new ContextExprCache<>(sortPolicy);
        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();

        ExprVar alloyX = makeTestVar("x");
        ExprVar alloyY = makeTestVar("y");
        Sort sort = Sort.mkSortConst("Sort");
        AnnotatedVar x = Term.mkVar("x").of(sort);

        context1.addTermMapping("x", new AnnotatedTerm(x));
        context2.addTermMapping("y", new AnnotatedTerm(x));

        // They should not remain distinct because they expand to the same thing.
        cache.put(alloyX, context1, 1);
        cache.put(alloyY, context2, 2);
        assertEquals(Integer.valueOf(2), cache.get(alloyX, context1));
        assertEquals(Integer.valueOf(2), cache.get(alloyY, context2));
    }

}