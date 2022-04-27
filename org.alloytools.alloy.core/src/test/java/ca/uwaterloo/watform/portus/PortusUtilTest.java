package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class PortusUtilTest {

    private ExprVar makeTestVar(String label) {
        return ExprVar.make(null, label);
    }

    @Test
    public void testIsDeclarationFormula_true_oneToAny() {
        // a in b one->c
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c");
        Expr expr = a.in(b.one_arrow_any(c));
        assertTrue(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_true_anyToOne() {
        // a in b->one c
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c");
        Expr expr = a.in(b.any_arrow_one(c));
        assertTrue(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_true_oneToOne() {
        // a in b one->one c
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c");
        Expr expr = a.in(b.one_arrow_one(c));
        assertTrue(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_true_nested1() {
        // a in b->(c one->one d)
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c"), d = makeTestVar("d");
        Expr expr = a.in(b.product(c.one_arrow_one(d)));
        assertTrue(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_true_nested2() {
        // a in (b some->c)->d
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c"), d = makeTestVar("d");
        Expr expr = a.in(b.some_arrow_any(c).product(d));
        assertTrue(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_false_notExprBinary() {
        assertFalse(PortusUtil.isDeclarationFormula(makeTestVar("a")));
    }

    @Test
    public void testIsDeclarationFormula_false_justMultiplicityArrow() {
        // a one->one b
        ExprVar a = makeTestVar("a"), b = makeTestVar("b");
        assertFalse(PortusUtil.isDeclarationFormula(a.one_arrow_one(b)));
    }

    @Test
    public void testIsDeclarationFormula_false_justIn() {
        // a in b
        ExprVar a = makeTestVar("a"), b = makeTestVar("b");
        assertFalse(PortusUtil.isDeclarationFormula(a.in(b)));
    }

    @Test
    public void testIsDeclarationFormula_false_inArrowNoMultiplicity() {
        // a in b->c, no multiplicities
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c");
        Expr expr = a.in(b.product(c));
        assertFalse(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_false_nestedNoMultiplicity() {
        // a in b->(c->d), no multiplicities
        ExprVar a = makeTestVar("a"), b = makeTestVar("b"), c = makeTestVar("c"), d = makeTestVar("d");
        Expr expr = a.in(b.product(c.product(d)));
        assertFalse(PortusUtil.isDeclarationFormula(expr));
    }

    @Test
    public void testIsDeclarationFormula_false_null() {
        //noinspection ConstantConditions
        assertFalse(PortusUtil.isDeclarationFormula(null));
    }

}