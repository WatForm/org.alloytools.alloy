package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class PortusUtilTest {

    private TranslationContext context;
    private SortPolicy policy;

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class, CALLS_REAL_METHODS);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        context = new TranslationContext(new PortusOptions(), mock(ScopeComputer.class), policy, mockRangeAssigner);
    }

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
        assertFalse(PortusUtil.isDeclarationFormula(null));
    }

    @Test
    public void testComputeFreeVariables_triviallyNone() {
        Sort sort = Sort.mkSortConst("S");
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Sig.Field field = sig.addField("field", sig);

        // none of these should have any free variables
        List<Expr> noFreeVars = Arrays.asList(
                ExprConstant.TRUE,
                ExprConstant.FALSE,
                ExprConstant.FALSE.not(),
                ExprConstant.FALSE.and(ExprConstant.TRUE),
                ExprConstant.IDEN,
                sig,
                sig.plus(sig),
                field,
                sig.join(field),
                ExprConstant.makeNUMBER(2),
                ExprConstant.makeNUMBER(2).iplus(ExprConstant.makeNUMBER(-2)));

        for (Expr expr : noFreeVars) {
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Test
    public void testComputeFreeVariables_var() {
        Sort sort = Sort.mkSortConst("S");
        ExprVar expr = makeTestVar("x");
        AnnotatedVar var = Var.apply("x").of(sort);
        context.addVarMapping("x", var);

        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertThat(result, containsInAnyOrder(var));
    }

    @Test
    public void testComputeFreeVariables_unaryOps() {
        Sort sort = Sort.mkSortConst("S");
        ExprVar expr = makeTestVar("x");
        AnnotatedVar var = Var.apply("x").of(sort);
        context.addVarMapping("x", var);

        // all these should just have var
        List<Expr> unaryOps = Arrays.asList(
                expr.no(),
                expr.one(),
                expr.lone(),
                expr.some(),
                expr.cast2int(),
                expr.cast2sigint(),
                ExprUnary.Op.NOOP.make(null, expr),
                expr.oneOf(),
                expr.loneOf(),
                expr.someOf(),
                expr.closure(),
                expr.reflexiveClosure(),
                expr.cardinality());
        for (Expr unaryOp : unaryOps) {
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(unaryOp, context);
            assertThat(result, containsInAnyOrder(var));
        }
    }

    @Test
    public void testComputeFreeVariables_binaryOps() {
        Sort sort = Sort.mkSortConst("S");
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addVarMapping("x", xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addVarMapping("y", yVar);

        // all these should have x and y
        @SuppressWarnings("SuspiciousNameCombination")
        List<Expr> binaryOps = Arrays.asList(
                x.plus(y),
                x.minus(y),
                x.intersect(y),
                x.join(y),
                x.product(y),
                // all the arrows (and indeed all binary ops) are treated the same
                x.any_arrow_some(y),
                x.lone_arrow_any(y),
                (x.product(y)).transpose(),
                x.lt(y),
                x.gt(y),
                x.lte(y),
                x.gte(y),
                x.equal(y),
                x.in(y),
                x.and(y),
                x.or(y),
                x.implies(y),
                x.iff(y),
                x.iplus(y),
                x.iminus(y),
                x.mul(y),
                x.div(y),
                x.shl(y),
                x.shr(y));
        for (Expr binaryOp : binaryOps) {
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(binaryOp, context);
            assertThat(result, containsInAnyOrder(xVar, yVar));
        }
    }

    @Test
    public void testComputeFreeVariables_ite() {
        Sort sort = Sort.mkSortConst("S");
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addVarMapping("x", xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addVarMapping("y", yVar);
        ExprVar z = makeTestVar("z");
        AnnotatedVar zVar = Var.apply("z").of(sort);
        context.addVarMapping("z", zVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.ite(y, z);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertThat(result, containsInAnyOrder(xVar, yVar, zVar));
    }

    @Test
    public void testComputeFreeVariables_exprElementOf() {
        Sort sort = Sort.mkSortConst("S");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addVarMapping("x", xVar);
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addVarMapping("y", yVar);
        ExprVar z = makeTestVar("z");
        AnnotatedVar zVar = Var.apply("z").of(sort);
        context.addVarMapping("z", zVar);

        Expr expr = ExprElementOf.make(new VarTuple(xVar, yVar), z);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertThat(result, containsInAnyOrder(xVar, yVar, zVar));
    }

    @Test
    public void testComputeFreeVariables_merge() {
        // the result should only contain one instance of each var
        Sort sort = Sort.mkSortConst("S");
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addVarMapping("x", xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addVarMapping("y", yVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.equal(y).and(y.equal(x)).and(x.in(x)).or(y.in(y));
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertThat(result, containsInAnyOrder(xVar, yVar));
    }

    @Test
    public void testComputeFreeVariables_quantifiers_1() {
        // quantifiers should take away the variables they quantify over from the list
        Sort sort = Sort.mkSortConst("S");
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Decl xDecl = sig.oneOf("x");
        ExprVar x = (ExprVar) xDecl.get();

        Expr expr = x.equal(x).forAll(xDecl);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertTrue(result.isEmpty());
    }

    @Test
    public void testComputeFreeVariables_quantifiers_2() {
        Sort sort = Sort.mkSortConst("S");
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Decl xDecl = sig.oneOf("x");
        ExprVar x = (ExprVar) xDecl.get();
        Decl yDecl = sig.oneOf("y");
        ExprVar y = (ExprVar) yDecl.get();
        AnnotatedVar yVar = Var.apply("yVar").of(sort);
        context.addVarMapping("y", yVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.equal(y).forAll(xDecl);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context);
        assertThat(result, containsInAnyOrder(yVar));
    }

}