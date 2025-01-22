package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class PortusUtilTest {

    private final Sort sort = Sort.mkSortConst("Sort");

    private TranslationContext context;
    private SortPolicy policy;

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class, CALLS_REAL_METHODS);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(sort));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(mock(ModelInfo.class), new ArrayList<>(), policy, mockScoper));
        context = new TranslationContext(new PortusOptions(), mockScoper, policy, mockRangeAssigner);
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
    public void testIsAncestorSig_unrelated() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        assertFalse(PortusUtil.isAncestorSig(sigA, sigB));
    }

    @Test
    public void testIsAncestorSig_equal() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        assertTrue(PortusUtil.isAncestorSig(sigA, sigA));
    }

    @Test
    public void testIsAncestorSig_child() {
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig(null, "Child", new Pos("", 0, 0), parent);
        assertTrue(PortusUtil.isAncestorSig(parent, child));
        assertFalse(PortusUtil.isAncestorSig(child, parent));
    }

    @Test
    public void testIsAncestorSig_grandchild() {
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig(null, "Child", new Pos("", 0, 0), parent);
        Sig.PrimSig grandchild = new Sig.PrimSig(null, "Grandchild", new Pos("", 0, 0), child);
        assertTrue(PortusUtil.isAncestorSig(parent, grandchild));
        assertTrue(PortusUtil.isAncestorSig(parent, child));
        assertTrue(PortusUtil.isAncestorSig(child, grandchild));
        assertFalse(PortusUtil.isAncestorSig(grandchild, parent));
        assertFalse(PortusUtil.isAncestorSig(grandchild, child));
        assertFalse(PortusUtil.isAncestorSig(child, parent));
    }

    @Test
    public void testIsAncestorSig_siblings() {
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child1 = new Sig.PrimSig(null, "Child1", new Pos("", 0, 0), parent);
        Sig.PrimSig child2 = new Sig.PrimSig(null, "Child2", new Pos("", 0, 0), parent);
        assertFalse(PortusUtil.isAncestorSig(child1, child2));
        assertFalse(PortusUtil.isAncestorSig(child2, child1));
    }

    @Test
    public void testMakeExhaustiveLookupTable_oneElement() {
        Term key = Term.mkVar("key");
        Term value = Term.mkVar("value");
        Term input = Term.mkVar("input");
        Term actual = PortusUtil.mkExhaustiveLookupTable(input, Collections.singletonList(new Pair<>(key, value)));
        assertEquals(value, actual);
    }

    @Test
    public void testMakeExhaustiveLookupTable_twoElements() {
        Term key1 = Term.mkVar("key1");
        Term value1 = Term.mkVar("value1");
        Term key2 = Term.mkVar("key2");
        Term value2 = Term.mkVar("value2");
        Term input = Term.mkVar("input");
        Term expected = Term.mkIfThenElse(Term.mkEq(input, key1), value1, value2);
        Term actual = PortusUtil.mkExhaustiveLookupTable(input, Arrays.asList(
                new Pair<>(key1, value1), new Pair<>(key2, value2)));
        assertEquals(expected, actual);
    }

    @Test
    public void testMakeExhaustiveLookupTable_threeElements() {
        Term key1 = Term.mkVar("key1");
        Term value1 = Term.mkVar("value1");
        Term key2 = Term.mkVar("key2");
        Term value2 = Term.mkVar("value2");
        Term key3 = Term.mkVar("key3");
        Term value3 = Term.mkVar("value3");
        Term input = Term.mkVar("input");
        Term expected = Term.mkIfThenElse(Term.mkEq(input, key1), value1,
                Term.mkIfThenElse(Term.mkEq(input, key2), value2, value3));
        Term actual = PortusUtil.mkExhaustiveLookupTable(input, Arrays.asList(
                new Pair<>(key1, value1), new Pair<>(key2, value2), new Pair<>(key3, value3)));
        assertEquals(expected, actual);
    }

    @Test
    public void testComputeFreeVariables_triviallyNone() {
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
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Test
    public void testComputeFreeVariables_var() {
        ExprVar expr = makeTestVar("x");
        AnnotatedVar var = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(var));
        context.addFortressVar(var);

        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertThat(result, containsInAnyOrder(var));
    }

    @Test
    public void testComputeFreeVariables_unaryOps() {
        ExprVar expr = makeTestVar("x");
        AnnotatedVar var = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(var));
        context.addFortressVar(var);

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
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(unaryOp, context, policy);
            assertThat(result, containsInAnyOrder(var));
        }
    }

    @Test
    public void testComputeFreeVariables_binaryOps() {
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(xVar));
        context.addFortressVar(xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addTermMapping("y", new AnnotatedTerm(yVar));
        context.addFortressVar(yVar);

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
            List<AnnotatedVar> result = PortusUtil.computeFreeVariables(binaryOp, context, policy);
            assertThat(result, containsInAnyOrder(xVar, yVar));
        }
    }

    @Test
    public void testComputeFreeVariables_ite() {
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(xVar));
        context.addFortressVar(xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addTermMapping("y", new AnnotatedTerm(yVar));
        context.addFortressVar(yVar);
        ExprVar z = makeTestVar("z");
        AnnotatedVar zVar = Var.apply("z").of(sort);
        context.addTermMapping("z", new AnnotatedTerm(zVar));
        context.addFortressVar(zVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.ite(y, z);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertThat(result, containsInAnyOrder(xVar, yVar, zVar));
    }

    @Test
    public void testComputeFreeVariables_exprElementOf() {
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(xVar));
        context.addFortressVar(xVar);
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addTermMapping("y", new AnnotatedTerm(yVar));
        context.addFortressVar(yVar);
        ExprVar z = makeTestVar("z");
        AnnotatedVar zVar = Var.apply("z").of(sort);
        context.addTermMapping("z", new AnnotatedTerm(zVar));
        context.addFortressVar(zVar);

        Expr expr = ExprElementOf.make(TermTuple.fromVars(xVar, yVar), z);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertThat(result, containsInAnyOrder(xVar, yVar, zVar));
    }

    @Test
    public void testComputeFreeVariables_merge() {
        // the result should only contain one instance of each var
        ExprVar x = makeTestVar("x");
        AnnotatedVar xVar = Var.apply("x").of(sort);
        context.addTermMapping("x", new AnnotatedTerm(xVar));
        context.addFortressVar(xVar);
        ExprVar y = makeTestVar("y");
        AnnotatedVar yVar = Var.apply("y").of(sort);
        context.addTermMapping("y", new AnnotatedTerm(yVar));
        context.addFortressVar(yVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.equal(y).and(y.equal(x)).and(x.in(x)).or(y.in(y));
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertThat(result, containsInAnyOrder(xVar, yVar));
    }

    @Test
    public void testComputeFreeVariables_quantifiers_1() {
        // quantifiers should take away the variables they quantify over from the list
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Decl xDecl = sig.oneOf("x");
        ExprVar x = (ExprVar) xDecl.get();

        Expr expr = x.equal(x).forAll(xDecl);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertTrue(result.isEmpty());
    }

    @Test
    public void testComputeFreeVariables_quantifiers_2() {
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Decl xDecl = sig.oneOf("x");
        ExprVar x = (ExprVar) xDecl.get();
        Decl yDecl = sig.oneOf("y");
        ExprVar y = (ExprVar) yDecl.get();
        AnnotatedVar yVar = Var.apply("yVar").of(sort);
        context.addTermMapping("y", new AnnotatedTerm(yVar));
        context.addFortressVar(yVar);

        @SuppressWarnings("SuspiciousNameCombination")
        Expr expr = x.equal(y).forAll(xDecl);
        List<AnnotatedVar> result = PortusUtil.computeFreeVariables(expr, context, policy);
        assertThat(result, containsInAnyOrder(yVar));
    }

    @Test
    public void testGetElement_Int_bitwidth3() {
        // test {getElement(i, Sort.Int()) : i = 0 to 7} = {-4, -3, -2, -1, 0, 1, 2, 3}
        Set<Value> elements = IntStream.range(0, 8)
                .mapToObj(i -> PortusUtil.getElement(i, Sort.Int()))
                .collect(Collectors.toSet());
        Set<Value> expected = IntStream.range(-4, 4)
                .mapToObj(IntegerLiteral::apply)
                .collect(Collectors.toSet());
        assertEquals(expected, elements);
    }

    @Test
    public void testGetElement_Int_bitwidth5() {
        // test {getElement(i, Sort.Int()) : i = 0 to 31} = {-16, -15, ..., 14, 15}
        Set<Value> elements = IntStream.range(0, 32)
                .mapToObj(i -> PortusUtil.getElement(i, Sort.Int()))
                .collect(Collectors.toSet());
        Set<Value> expected = IntStream.range(-16, 16)
                .mapToObj(IntegerLiteral::apply)
                .collect(Collectors.toSet());
        assertEquals(expected, elements);
    }

    @Test
    public void testGetElement_nonInt_zeroIndexed() {
        // test getElement(0, Sort) = @1Sort
        Value actual = PortusUtil.getElement(0, sort);
        assertEquals(Term.mkDomainElement(1, sort), actual);
    }

    @Test
    public void testExpandLets_simple() {
        // test that if x is mapped to y in the var mapping context, x expands to y
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        VarMappingContext varMappingContext = new VarMappingContext();
        varMappingContext.addLetMapping("x", y);

        Expr expanded = PortusUtil.expandLets(x, varMappingContext, policy);
        assertEquals(y, expanded);
    }

    @Test
    public void testExpandLets_twoLevels() {
        // if the var mapping context maps y->z and x->y then x should expand to z
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = makeTestVar("z");
        VarMappingContext varMappingContext = new VarMappingContext();
        varMappingContext.addLetMapping("y", z);
        varMappingContext.addLetMapping("x", y);

        Expr expanded = PortusUtil.expandLets(x, varMappingContext, policy);
        assertEquals(z, expanded);
    }

    @Test
    public void testExpandLets_withLet() {
        // test "let x = y | x" gets expanded to "y" (the let gets replaced)
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        VarMappingContext varMappingContext = new VarMappingContext();

        Expr letExpr = ExprLet.make(null, x, y, x);
        Expr expanded = PortusUtil.expandLets(letExpr, varMappingContext, policy);
        assertEquals(y, expanded);
    }

    @Test
    public void testExpandLets_unchanged() {
        // test that expandLets reconstructs a variety of expressions properly
        Sig.PrimSig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(sort);
        Sig.Field field = sig.addField("field", ExprConstant.ONE);
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = ExprVar.make(null, "z", Type.make(sig));
        Func f = new Func(null, null, "f", Collections.singletonList(z.oneOf("x")), z, x);

        @SuppressWarnings("SuspiciousNameCombination")
        List<Expr> testExprs = Arrays.asList(
                // Binary ops
                x.plus(y),
                x.minus(y),
                x.intersect(y),
                x.join(y),
                x.product(y),
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
                x.shr(y),
                // Unary ops
                x.not(),
                x.transpose(),
                x.no(),
                x.one(),
                x.some(),
                x.lone(),
                x.oneOf(),
                x.someOf(),
                x.loneOf(),
                x.closure(),
                x.reflexiveClosure(),
                x.cardinality(),
                x.cast2int(),
                x.cast2sigint(),
                ExprUnary.Op.NOOP.make(null, x),
                // Constants
                ExprConstant.TRUE,
                ExprConstant.FALSE,
                ExprConstant.IDEN,
                ExprConstant.EMPTYNESS,
                ExprConstant.MAX,
                ExprConstant.MIN,
                ExprConstant.ONE,
                ExprConstant.ZERO,
                // Quantifier expressions
                x.equal(y).forAll(z.oneOf("x")),
                x.equal(y).forSome(z.oneOf("x")),
                x.equal(y).forLone(z.oneOf("x")),
                x.equal(y).forOne(z.oneOf("x")),
                x.equal(y).forNo(z.oneOf("x")),
                x.equal(y).forAll(z.oneOf("x")).forSome(z.oneOf("y")),
                // Misc
                x.ite(y, z),
                sig,
                field,
                ExprElementOf.make(Term.mkVar("t").of(sort), x),
                // We don't expand ExprCalls
                ExprCall.make(null, null, f, Collections.singletonList(y), 0L));
        for (Expr expr : testExprs) {
            Expr expanded = PortusUtil.expandLets(expr, new VarMappingContext(), policy);
            assertTrue(PortusUtil.areExprsEqual(expr, expanded));
        }
    }

    @Test
    public void testAreExprsEqual_basicConstants() {
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.TRUE, ExprConstant.TRUE));
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.TRUE, ExprConstant.FALSE));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.IDEN, ExprConstant.IDEN));
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.IDEN, ExprConstant.EMPTYNESS));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.EMPTYNESS, ExprConstant.EMPTYNESS));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.MAX, ExprConstant.MAX));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.MIN, ExprConstant.MIN));
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.MAX, ExprConstant.MIN));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.NEXT, ExprConstant.NEXT));
    }

    @Test
    public void testAreExprsEqual_integers() {
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.ZERO, ExprConstant.ZERO));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.ONE, ExprConstant.ONE));
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.ZERO, ExprConstant.ONE));
        assertTrue(PortusUtil.areExprsEqual(ExprConstant.makeNUMBER(5), ExprConstant.makeNUMBER(5)));
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.makeNUMBER(5), ExprConstant.makeNUMBER(-5)));

        // not even under default bitwidth modulus
        assertFalse(PortusUtil.areExprsEqual(ExprConstant.makeNUMBER(0), ExprConstant.makeNUMBER(64)));
    }

    @Test
    public void testAreExprsEqual_strings() {
        Function<String, Expr> makeString = str -> ExprConstant.Op.STRING.make(null, str);
        assertTrue(PortusUtil.areExprsEqual(makeString.apply("foo"), makeString.apply("foo")));
        assertFalse(PortusUtil.areExprsEqual(makeString.apply("foo"), makeString.apply("bar")));
        assertTrue(PortusUtil.areExprsEqual(makeString.apply(""), makeString.apply("")));
        assertFalse(PortusUtil.areExprsEqual(makeString.apply(""), makeString.apply(" ")));
    }

    @Test
    public void testAreExprsEqual_var() {
        ExprVar sameVar = makeTestVar("sameVar");
        assertTrue(PortusUtil.areExprsEqual(sameVar, sameVar));
        assertTrue(PortusUtil.areExprsEqual(makeTestVar("x"), makeTestVar("x"))); // same label
        assertFalse(PortusUtil.areExprsEqual(makeTestVar("x"), makeTestVar("y"))); // different labels

        // even with different pos
        ExprVar varWithPos1 = ExprVar.make(new Pos("abc.als", 10, 23), "foo");
        ExprVar varWithPos2 = ExprVar.make(new Pos("def.als", 653, 1), "foo");
        ExprVar varWithNullPos = ExprVar.make(null, "foo");
        assertTrue(PortusUtil.areExprsEqual(varWithPos1, varWithPos2));
        assertTrue(PortusUtil.areExprsEqual(varWithPos1, varWithNullPos));
        assertTrue(PortusUtil.areExprsEqual(varWithPos2, varWithNullPos));
    }

    @Test
    public void testAreExprsEqual_unaryOps() {
        ExprVar x = makeTestVar("x");
        assertTrue(PortusUtil.areExprsEqual(x.transpose(), x.transpose()));
        assertTrue(PortusUtil.areExprsEqual(x.cardinality(), x.cardinality()));
        assertTrue(PortusUtil.areExprsEqual(x.closure(), x.closure()));
        assertTrue(PortusUtil.areExprsEqual(x.reflexiveClosure(), x.reflexiveClosure()));
        assertFalse(PortusUtil.areExprsEqual(x.closure(), x.reflexiveClosure()));
        assertTrue(PortusUtil.areExprsEqual(x.not(), x.not()));
        assertFalse(PortusUtil.areExprsEqual(x.not(), x.no()));
        assertTrue(PortusUtil.areExprsEqual(x.no(), x.no()));
        assertTrue(PortusUtil.areExprsEqual(x.some(), x.some()));
        assertTrue(PortusUtil.areExprsEqual(x.lone(), x.lone()));
        assertTrue(PortusUtil.areExprsEqual(x.one(), x.one()));
        assertFalse(PortusUtil.areExprsEqual(x.no(), x.one()));
        assertFalse(PortusUtil.areExprsEqual(x.no(), x.lone()));
        assertFalse(PortusUtil.areExprsEqual(x.some(), x.lone()));
        assertTrue(PortusUtil.areExprsEqual(x.oneOf(), x.oneOf()));
        assertTrue(PortusUtil.areExprsEqual(x.loneOf(), x.loneOf()));
        assertTrue(PortusUtil.areExprsEqual(x.setOf(), x.setOf()));
        assertTrue(PortusUtil.areExprsEqual(x.someOf(), x.someOf()));
        assertFalse(PortusUtil.areExprsEqual(x.oneOf(), x.one()));
        assertFalse(PortusUtil.areExprsEqual(x.loneOf(), x.lone()));
        assertFalse(PortusUtil.areExprsEqual(x.someOf(), x.some()));

        ExprVar y = makeTestVar("y");
        assertFalse(PortusUtil.areExprsEqual(x.not(), y.not()));
        assertFalse(PortusUtil.areExprsEqual(x.transpose(), y.transpose()));
        assertFalse(PortusUtil.areExprsEqual(x.closure(), y.closure()));
    }

    @Test
    @SuppressWarnings("SuspiciousNameCombination")
    public void testAreExprsEqual_binaryOps() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");

        assertTrue(PortusUtil.areExprsEqual(x.and(y), x.and(y)));
        assertTrue(PortusUtil.areExprsEqual(x.or(y), x.or(y)));
        assertTrue(PortusUtil.areExprsEqual(x.implies(y), x.implies(y)));
        assertTrue(PortusUtil.areExprsEqual(x.iff(y), x.iff(y)));
        assertTrue(PortusUtil.areExprsEqual(x.plus(y), x.plus(y)));
        assertTrue(PortusUtil.areExprsEqual(x.minus(y), x.minus(y)));
        assertTrue(PortusUtil.areExprsEqual(x.intersect(y), x.intersect(y)));
        assertTrue(PortusUtil.areExprsEqual(x.domain(y), x.domain(y)));
        assertTrue(PortusUtil.areExprsEqual(x.range(y), x.range(y)));
        assertTrue(PortusUtil.areExprsEqual(x.iplus(y), x.iplus(y)));
        assertTrue(PortusUtil.areExprsEqual(x.iminus(y), x.iminus(y)));
        assertTrue(PortusUtil.areExprsEqual(x.mul(y), x.mul(y)));
        assertTrue(PortusUtil.areExprsEqual(x.div(y), x.div(y)));
        assertTrue(PortusUtil.areExprsEqual(x.rem(y), x.rem(y)));
        assertTrue(PortusUtil.areExprsEqual(x.in(y), x.in(y)));
        assertTrue(PortusUtil.areExprsEqual(x.equal(y), x.equal(y)));
        assertFalse(PortusUtil.areExprsEqual(x.equal(y), x.in(y)));
        assertTrue(PortusUtil.areExprsEqual(x.gt(y), x.gt(y)));
        assertFalse(PortusUtil.areExprsEqual(x.gt(y), x.gte(y)));
        assertTrue(PortusUtil.areExprsEqual(x.gte(y), x.gte(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lt(y), x.lt(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lte(y), x.lte(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lte(y), x.lte(y)));
        assertFalse(PortusUtil.areExprsEqual(x.lte(y), x.lt(y)));
        assertFalse(PortusUtil.areExprsEqual(x.gt(y), x.lt(y)));

        assertTrue(PortusUtil.areExprsEqual(x.product(y), x.product(y)));
        assertTrue(PortusUtil.areExprsEqual(x.any_arrow_one(y), x.any_arrow_one(y)));
        assertTrue(PortusUtil.areExprsEqual(x.any_arrow_lone(y), x.any_arrow_lone(y)));
        assertTrue(PortusUtil.areExprsEqual(x.any_arrow_some(y), x.any_arrow_some(y)));
        assertTrue(PortusUtil.areExprsEqual(x.one_arrow_any(y), x.one_arrow_any(y)));
        assertTrue(PortusUtil.areExprsEqual(x.one_arrow_one(y), x.one_arrow_one(y)));
        assertTrue(PortusUtil.areExprsEqual(x.one_arrow_lone(y), x.one_arrow_lone(y)));
        assertTrue(PortusUtil.areExprsEqual(x.one_arrow_some(y), x.one_arrow_some(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lone_arrow_any(y), x.lone_arrow_any(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lone_arrow_one(y), x.lone_arrow_one(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lone_arrow_lone(y), x.lone_arrow_lone(y)));
        assertTrue(PortusUtil.areExprsEqual(x.lone_arrow_some(y), x.lone_arrow_some(y)));
        assertTrue(PortusUtil.areExprsEqual(x.some_arrow_any(y), x.some_arrow_any(y)));
        assertTrue(PortusUtil.areExprsEqual(x.some_arrow_one(y), x.some_arrow_one(y)));
        assertTrue(PortusUtil.areExprsEqual(x.some_arrow_lone(y), x.some_arrow_lone(y)));
        assertTrue(PortusUtil.areExprsEqual(x.some_arrow_some(y), x.some_arrow_some(y)));
        assertFalse(PortusUtil.areExprsEqual(x.any_arrow_one(y), x.any_arrow_lone(y)));
        assertFalse(PortusUtil.areExprsEqual(x.product(y), x.any_arrow_one(y)));
        assertFalse(PortusUtil.areExprsEqual(x.one_arrow_one(y), x.one_arrow_any(y)));
        assertFalse(PortusUtil.areExprsEqual(x.lone_arrow_one(y), x.lone_arrow_lone(y)));
        assertFalse(PortusUtil.areExprsEqual(x.any_arrow_one(y), x.lone_arrow_lone(y)));
        assertFalse(PortusUtil.areExprsEqual(x.some_arrow_some(y), x.some_arrow_one(y)));
        assertFalse(PortusUtil.areExprsEqual(x.some_arrow_some(y), x.any_arrow_some(y)));
    }

    @Test
    @SuppressWarnings("SuspiciousNameCombination")
    public void testAreExprsEqual_noCommutativity() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");

        // x && y !== y && x, and similar: no commutativity simplifications
        assertFalse(PortusUtil.areExprsEqual(x.and(y), y.and(x)));
        assertFalse(PortusUtil.areExprsEqual(x.or(y), y.or(x)));
        assertFalse(PortusUtil.areExprsEqual(x.iff(y), y.iff(x)));
        assertFalse(PortusUtil.areExprsEqual(x.plus(y), y.plus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.intersect(y), y.intersect(x)));
        assertFalse(PortusUtil.areExprsEqual(x.iplus(y), y.iplus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.iminus(y), y.iminus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.mul(y), y.mul(x)));
        assertFalse(PortusUtil.areExprsEqual(x.equal(y), y.equal(x)));
    }

    @Test
    public void testAreExprsEqual_noAssociativity() {
        ExprVar x = makeTestVar("x");

        // (x + x) + x !== x + (x + x), and similar: no associativity simplifications
        // Note: ExprList for AND and OR performs flattening
        assertFalse(PortusUtil.areExprsEqual(x.plus(x.plus(x)), (x.plus(x)).plus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.intersect(x.intersect(x)), (x.intersect(x)).intersect(x)));
        assertFalse(PortusUtil.areExprsEqual(x.iplus(x.iplus(x)), (x.iplus(x)).iplus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.iminus(x.iminus(x)), (x.iminus(x)).iminus(x)));
        assertFalse(PortusUtil.areExprsEqual(x.mul(x.mul(x)), (x.mul(x)).mul(x)));
        assertFalse(PortusUtil.areExprsEqual(x.product(x.product(x)), (x.product(x)).product(x)));
    }

    @Test
    @SuppressWarnings("SuspiciousNameCombination")
    public void testAreExprsEqual_ite() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = makeTestVar("z");
        assertTrue(PortusUtil.areExprsEqual(x.ite(y, z), x.ite(y, z)));
        assertFalse(PortusUtil.areExprsEqual(x.ite(y, z), x.ite(z, y)));
        assertFalse(PortusUtil.areExprsEqual(y.ite(y, z), x.ite(y, z)));
        assertFalse(PortusUtil.areExprsEqual(x.ite(x, z), x.ite(y, z)));
        assertFalse(PortusUtil.areExprsEqual(x.ite(y, x), x.ite(y, z)));
    }

    @Test
    public void testAreExprsEqual_list() {
        ExprVar x = makeTestVar("x");

        // AND and OR are implemented as ExprList.
        assertTrue(PortusUtil.areExprsEqual(x.and(x), x.and(x)));
        assertTrue(PortusUtil.areExprsEqual(x.and(x).and(x), x.and(x).and(x)));
        assertFalse(PortusUtil.areExprsEqual(x.and(x).and(x), x.and(x)));
        assertFalse(PortusUtil.areExprsEqual(x.and(x), x.and(x).and(x)));
    }

    @Test
    public void testAreExprsEqual_sig() {
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        Sig sigASubset = new Sig.SubsetSig(null, "A", null, Collections.singletonList(sigB));

        assertTrue(PortusUtil.areExprsEqual(sigA, sigA));
        assertFalse(PortusUtil.areExprsEqual(sigA, sigB));

        // Sigs are compared *only* on their labels
        assertTrue(PortusUtil.areExprsEqual(sigA, sigASubset));
        assertFalse(PortusUtil.areExprsEqual(sigB, sigASubset));
    }

    @Test
    public void testAreExprsEqual_field() {
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        Sig sigASubset = new Sig.SubsetSig(null, "A", null, Collections.singletonList(sigB));

        Sig.Field fieldA1 = sigA.addField("f", ExprConstant.ONE);
        Sig.Field fieldA2 = sigA.addField("g", ExprConstant.ONE);
        Sig.Field fieldB = sigB.addField("f", ExprConstant.ONE);
        Sig.Field fieldASubset = sigASubset.addField("f", ExprConstant.EMPTYNESS);

        // Fields are compared *only* on label + parent sig label (and *not* on bounding expr)
        assertTrue(PortusUtil.areExprsEqual(fieldA1, fieldA1));
        assertTrue(PortusUtil.areExprsEqual(fieldA2, fieldA2));
        assertFalse(PortusUtil.areExprsEqual(fieldA1, fieldA2));
        assertFalse(PortusUtil.areExprsEqual(fieldA1, fieldB));
        assertTrue(PortusUtil.areExprsEqual(fieldA1, fieldASubset)); // !!
    }

    @Test
    public void testAreExprsEqual_quantifier() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar w = makeTestVar("w");
        assertTrue(PortusUtil.areExprsEqual(x.forAll(y.oneOf("z")), x.forAll(y.oneOf("z"))));
        assertTrue(PortusUtil.areExprsEqual(x.forSome(y.oneOf("z")), x.forSome(y.oneOf("z"))));
        assertTrue(PortusUtil.areExprsEqual(x.forLone(y.oneOf("z")), x.forLone(y.oneOf("z"))));
        assertTrue(PortusUtil.areExprsEqual(x.forOne(y.oneOf("z")), x.forOne(y.oneOf("z"))));
        assertTrue(PortusUtil.areExprsEqual(x.forNo(y.oneOf("z")), x.forNo(y.oneOf("z"))));
        assertTrue(PortusUtil.areExprsEqual(x.comprehensionOver(y.oneOf("z")), x.comprehensionOver(y.oneOf("z"))));
        assertFalse(PortusUtil.areExprsEqual(x.forAll(y.oneOf("z")), x.forNo(y.oneOf("z"))));
        assertFalse(PortusUtil.areExprsEqual(x.forSome(y.oneOf("z")), x.forLone(y.oneOf("z"))));
        assertFalse(PortusUtil.areExprsEqual(x.forAll(y.oneOf("w")), x.forAll(y.oneOf("z"))));
        assertFalse(PortusUtil.areExprsEqual(x.forAll(w.oneOf("z")), x.forAll(y.oneOf("z"))));
        assertFalse(PortusUtil.areExprsEqual(w.forAll(y.oneOf("z")), x.forAll(y.oneOf("z"))));

        assertTrue(PortusUtil.areExprsEqual(
                x.forAll(y.oneOf("z"), y.oneOf("k")), x.forAll(y.oneOf("z"), y.oneOf("k"))));
        assertFalse(PortusUtil.areExprsEqual(x.forAll(y.oneOf("z")), x.forAll(y.oneOf("z"), y.oneOf("k"))));
    }

    @Test
    public void testAreExprsEqual_let() {
        // Purely syntactic
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = makeTestVar("z");
        ExprVar w = makeTestVar("w");
        assertTrue(PortusUtil.areExprsEqual(ExprLet.make(null, x, y, z), ExprLet.make(null, x, y, z)));
        assertFalse(PortusUtil.areExprsEqual(ExprLet.make(null, x, y, w), ExprLet.make(null, x, y, z)));
        assertFalse(PortusUtil.areExprsEqual(ExprLet.make(null, x, w, z), ExprLet.make(null, x, y, z)));
        assertFalse(PortusUtil.areExprsEqual(ExprLet.make(null, w, y, z), ExprLet.make(null, x, y, z)));
    }

    @Test
    public void testAreExprsEqual_call() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = makeTestVar("z");
        Func predF = new Func(null, null, "f", Collections.emptyList(), null, x);
        Func funcF = new Func(null, null, "f", Collections.emptyList(), y, x);
        Func predG = new Func(null, null, "g", Collections.emptyList(), null, x);
        Func predFArgs1 = new Func(null, null, "f", Collections.singletonList(y.oneOf("k")), null, x);
        Func predFArgs2 = new Func(null, null, "f", Collections.singletonList(y.oneOf("l")), null, x);
        Func predFArgs3 = new Func(
                null, null, "f", Arrays.asList(y.oneOf("k"), y.oneOf("l")), null, x);

        assertTrue(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L)));
        // Weight doesn't matter
        assertTrue(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                ExprCall.make(null, null, predF, Collections.emptyList(), 1L)));

        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                ExprCall.make(null, null, funcF, Collections.emptyList(), 0L)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                ExprCall.make(null, null, predG, Collections.emptyList(), 0L)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                ExprCall.make(null, null, predFArgs1, Collections.singletonList(y), 0L)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                ExprCall.make(null, null, predFArgs2, Collections.singletonList(z), 0L)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                ExprCall.make(null, null, predFArgs3, Arrays.asList(z, y), 0L)));
    }

    @Test
    public void testAreExprsEqual_elementOf() {
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        Sort sort2 = Sort.mkSortConst("Sort2");
        AnnotatedVar fortressX = Term.mkVar("fx").of(sort);
        AnnotatedVar fortressXSort2 = Term.mkVar("fx").of(sort2);
        AnnotatedVar fortressY = Term.mkVar("fy").of(sort);

        assertTrue(PortusUtil.areExprsEqual(
                ExprElementOf.make(fortressX, x), ExprElementOf.make(fortressX, x)));
        assertTrue(PortusUtil.areExprsEqual(
                ExprElementOf.make(new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x),
                ExprElementOf.make(new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprElementOf.make(fortressY, x), ExprElementOf.make(fortressX, x)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprElementOf.make(fortressX, y), ExprElementOf.make(fortressX, x)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprElementOf.make(fortressXSort2, x), ExprElementOf.make(fortressX, x)));
        assertFalse(PortusUtil.areExprsEqual(
                ExprElementOf.make(new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x),
                ExprElementOf.make(fortressX, x)));
    }

    @Test
    public void testAreExprsEqual_noops() {
        ExprVar x = makeTestVar("x");
        assertTrue(PortusUtil.areExprsEqual(x, ExprUnary.Op.NOOP.make(null, x)));
        assertTrue(PortusUtil.areExprsEqual(ExprUnary.Op.NOOP.make(null, x), x));
        assertTrue(PortusUtil.areExprsEqual(x, x.cast2int()));
        assertTrue(PortusUtil.areExprsEqual(x.cast2int(), x));
        assertTrue(PortusUtil.areExprsEqual(x, x.cast2sigint()));
        assertTrue(PortusUtil.areExprsEqual(x.cast2sigint(), x));
        assertTrue(PortusUtil.areExprsEqual(
                ExprUnary.Op.NOOP.make(null, x).plus(x.cast2int().cast2sigint()),
                x.plus(ExprUnary.Op.NOOP.make(null, x.cast2int()))));
    }

    @Test
    public void testAreExprsEqual_null() {
        ExprVar x = makeTestVar("x");
        assertTrue(PortusUtil.areExprsEqual(null, null));
        assertFalse(PortusUtil.areExprsEqual(x, null));
        assertFalse(PortusUtil.areExprsEqual(null, x));
    }

    @Test
    public void testAreExprsEqual_termMappings() {
        // Test the context functionality - map to the same term, should compare equal.
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        AnnotatedVar fortressX = Term.mkVar("fx").of(sort);

        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();
        context1.addTermMapping("x", new AnnotatedTerm(fortressX));
        context2.addTermMapping("y", new AnnotatedTerm(fortressX));

        assertTrue(PortusUtil.areExprsEqual(x, y, context1, context2));
        assertFalse(PortusUtil.areExprsEqual(x, x, context1, context2)); // only one maps correctly
        assertFalse(PortusUtil.areExprsEqual(y, y, context1, context2)); // only one maps correctly
    }

    @Test
    @SuppressWarnings("SuspiciousNameCombination")
    public void testExprHashCode() {
        // For a large list of expressions, test the invariant:
        // exprHashCode(expr1) == exprHashCode(expr2) iff areExprsEqual(expr1, expr2).
        // It's possible that we get unlucky and get a hash collision, but these are simple enough
        // expressions that that should be considered a bug in exprHashCode.

        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        ExprVar z = makeTestVar("z");
        Func predF = new Func(null, null, "f", Collections.emptyList(), null, x);
        Func funcF = new Func(null, null, "f", Collections.emptyList(), y, x);
        Func predG = new Func(null, null, "g", Collections.emptyList(), null, x);
        Func predFArgs1 = new Func(null, null, "f", Collections.singletonList(y.oneOf("k")), null, x);
        Func predFArgs2 = new Func(null, null, "f", Collections.singletonList(y.oneOf("l")), null, x);
        Func predFArgs3 = new Func(
                null, null, "f", Arrays.asList(y.oneOf("k"), y.oneOf("l")), null, x);
        Sort sort2 = Sort.mkSortConst("Sort2");
        AnnotatedVar fortressX = Term.mkVar("fx").of(sort);
        AnnotatedVar fortressXSort2 = Term.mkVar("fx").of(sort2);
        AnnotatedVar fortressY = Term.mkVar("fy").of(sort);

        @SuppressWarnings("RedundantTypeArguments (explicit type arguments speedup compilation and analysis time)")
        List<Pair<Expr, Expr>> testExprs = Arrays.<Pair<Expr, Expr>> asList(
                new Pair<>(x, x),
                new Pair<>(makeTestVar("x"), makeTestVar("x")),
                new Pair<>(x, y),
                new Pair<>(x, ExprVar.make(new Pos("abc.als", 10, 45), "x")),
                new Pair<>(x.and(y), x.and(y)),
                new Pair<>(x.and(y), y.and(x)),
                new Pair<>(x.and(y), x.or(y)),
                new Pair<>(x.and(x), x.and(x).and(x)),
                new Pair<>(x.plus(y), x.plus(y)),
                new Pair<>(x.plus(y), y.plus(x)),
                new Pair<>(x.plus(x.plus(x)), x.plus(x).plus(x)),
                new Pair<>(x.plus(y), x.minus(y)),
                new Pair<>(x, x.transpose()),
                new Pair<>(x.transpose(), makeTestVar("x").transpose()),
                new Pair<>(x.closure(), x.closure()),
                new Pair<>(x.closure(), x.reflexiveClosure()),
                new Pair<>(x.one(), x.oneOf()),
                new Pair<>(x.product(y), x.product(y)),
                new Pair<>(x.product(y), x.any_arrow_one(y)),
                new Pair<>(x.one_arrow_lone(y), x.one_arrow_some(y)),
                new Pair<>(x.ite(y, z), x.ite(y, z)),
                new Pair<>(x.ite(y, z), x.ite(z, y)),
                new Pair<>(x.ite(y, z), x.ite(y, x)),
                new Pair<>(x.ite(y, z), y.ite(y, z)),
                new Pair<>(ExprLet.make(null, x, y, z), ExprLet.make(null, x, y, z)),
                new Pair<>(ExprLet.make(null, x, y, z), ExprLet.make(new Pos("foo.als", 53, 1), x, y, z)),
                new Pair<>(ExprLet.make(null, x, y, z), ExprLet.make(null, x, z, y)),
                new Pair<>(ExprLet.make(null, x, y, z), ExprLet.make(null, z, y, z)),
                new Pair<>(x.forAll(y.oneOf("z")), x.forAll(y.oneOf("z"))),
                new Pair<>(x.forAll(y.oneOf("z")), x.forAll(y.oneOf("k"))),
                new Pair<>(x.forAll(y.oneOf("z")), x.forAll(y.oneOf("z"), y.oneOf("k"))),
                new Pair<>(x.forAll(y.oneOf("z")), x.forSome(y.oneOf("z"))),
                new Pair<>(x.forAll(y.oneOf("z")), x.forNo(y.oneOf("z"))),
                new Pair<>(x.forNo(y.oneOf("z")), x.forNo(y.oneOf("z"))),
                new Pair<>(x.forAll(y.oneOf("z")), x.forAll(z.oneOf("z"))),
                new Pair<>(ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                        ExprCall.make(null, null, predF, Collections.emptyList(), 0L)),
                new Pair<>(ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                        ExprCall.make(null, null, predF, Collections.emptyList(), 1L)),
                new Pair<>(ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                        ExprCall.make(null, null, funcF, Collections.emptyList(), 0L)),
                new Pair<>(ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                        ExprCall.make(null, null, predG, Collections.emptyList(), 0L)),
                new Pair<>(ExprCall.make(null, null, predF, Collections.emptyList(), 0L),
                        ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L)),
                new Pair<>(ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                        ExprCall.make(null, null, predFArgs1, Collections.singletonList(y), 0L)),
                new Pair<>(ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                        ExprCall.make(null, null, predFArgs2, Collections.singletonList(z), 0L)),
                new Pair<>(ExprCall.make(null, null, predFArgs1, Collections.singletonList(z), 0L),
                        ExprCall.make(null, null, predFArgs3, Arrays.asList(z, y), 0L)),
                new Pair<>(ExprElementOf.make(fortressX, x), ExprElementOf.make(fortressX, x)),
                new Pair<>(
                        ExprElementOf.make(
                                new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x),
                        ExprElementOf.make(
                                new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x)),
                new Pair<>(ExprElementOf.make(fortressY, x), ExprElementOf.make(fortressX, x)),
                new Pair<>(ExprElementOf.make(fortressX, y), ExprElementOf.make(fortressX, x)),
                new Pair<>(ExprElementOf.make(fortressXSort2, x), ExprElementOf.make(fortressX, x)),
                new Pair<>(
                        ExprElementOf.make(
                                new TermTuple(new AnnotatedTerm(fortressX), new AnnotatedTerm(fortressY)), x),
                        ExprElementOf.make(fortressX, x)),
                new Pair<>(x, ExprUnary.Op.NOOP.make(null, x)),
                new Pair<>(ExprUnary.Op.NOOP.make(null, x), x),
                new Pair<>(x, x.cast2int()),
                new Pair<>(x.cast2int(), x),
                new Pair<>(x, x.cast2sigint()),
                new Pair<>(x.cast2sigint(), x),
                new Pair<>(ExprUnary.Op.NOOP.make(null, x).plus(x.cast2int().cast2sigint()),
                        x.plus(ExprUnary.Op.NOOP.make(null, x.cast2int()))),
                new Pair<>(null, null),
                new Pair<>(null, x),
                new Pair<>(x, null));

        for (Pair<Expr, Expr> testExprPair : testExprs) {
            Expr expr1 = testExprPair.a;
            Expr expr2 = testExprPair.b;
            if (PortusUtil.areExprsEqual(expr1, expr2)) {
                assertEquals(PortusUtil.exprHashCode(expr1), PortusUtil.exprHashCode(expr2));
            } else {
                assertNotEquals(PortusUtil.exprHashCode(expr1), PortusUtil.exprHashCode(expr2));
            }
        }
    }

    @Test
    public void testExprHashCode_termMapping() {
        // map to the same term, should have the same hash code.
        ExprVar x = makeTestVar("x");
        ExprVar y = makeTestVar("y");
        AnnotatedVar fortressX = Term.mkVar("fx").of(sort);

        VarMappingContext context1 = new VarMappingContext();
        VarMappingContext context2 = new VarMappingContext();
        context1.addTermMapping("x", new AnnotatedTerm(fortressX));
        context2.addTermMapping("y", new AnnotatedTerm(fortressX));

        assertEquals(PortusUtil.exprHashCode(x, context1), PortusUtil.exprHashCode(y, context2));
        assertNotEquals(PortusUtil.exprHashCode(x, context1), PortusUtil.exprHashCode(x, context2));
        assertNotEquals(PortusUtil.exprHashCode(y, context1), PortusUtil.exprHashCode(y, context2));
    }

}