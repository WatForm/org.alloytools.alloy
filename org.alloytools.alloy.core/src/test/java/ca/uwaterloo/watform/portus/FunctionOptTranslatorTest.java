package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;

import java.util.ArrayList;
import java.util.Arrays;

import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class FunctionOptTranslatorTest {

    // Some test sorts
    private final Sort sortA = Sort.mkSortConst("sortA");
    private final Sort sortB = Sort.mkSortConst("sortB");
    private final Sort sortC = Sort.mkSortConst("sortC");

    private Translator mockRoot;
    private ScalarCaster mockScalarCaster;
    private Evaluator mockEvaluator;

    private SortPolicy mockSortPolicy;
    private TranslationContext context;

    /** For use in Mockito then() with a translate() call: map (x1,...,xn) \in expr to funcName(x1,...,xn). */
    private Answer<Term> useTestFunction(String funcName, Expr expr) {
        return ctx -> {
            Expr argExpr = ctx.getArgument(0);
            assertTrue(argExpr instanceof ExprElementOf);
            ExprElementOf elementOf = (ExprElementOf) argExpr;
            assertEquals(expr, elementOf.sub);
            return Term.mkApp(funcName, elementOf.tuple.getTerms());
        };
    }

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockScalarCaster = mock(ScalarCaster.class);
        mockEvaluator = mock(Evaluator.class);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(
                Theory.empty().withSort(sortA).withSort(sortB).withSort(sortC).withSort(Sort.Int()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(new ArrayList<>(), mockSortPolicy, mockScoper));
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_inapplicable() {
        // test "sig A { f: set B }" doesn't apply the opt
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.setOf());
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_lone_inapplicable() {
        // test "sig A { f: lone B }" doesn't apply the opt when it's off
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.loneOf());
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, false);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_one() {
        // test translating "sig A { f: one B }" leads to:
        // - function f: sort(A)->sort(B)
        // - axiom "forall x: sort(A) . inA(x) => inB(f(x))"
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        // even when lone opt is on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        // should have one function and one axiom
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl func = theory.functionDeclarations().head();
        assertEquals(1, func.arity());
        assertEquals(sortA, func.argSorts().head());
        assertEquals(sortB, func.resultSort());

        Var x = Term.mkVar("x0_0");
        Term expectedAxiom = Term.mkForall(x.of(sortA), Term.mkImp(
                Term.mkApp("inA", x),
                Term.mkApp("inB", Term.mkApp(func.name(), x))));
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_lone() {
        // test translating "sig A { f: one B }" leads to:
        // - function f: sort(A)->sort(B)
        // - domain predicate inDomain: sort(A)->bool
        // - axiom "forall x: sort(A) . inDomain(x) => inB(f(x))"
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.loneOf());

        // lone opt must be on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        // should have two functions and one axiom
        Theory theory = context.getTheory();
        assertEquals(2, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl func = theory.functionDeclarations().head();
        assertEquals(1, func.arity());
        assertEquals(sortA, func.argSorts().head());
        assertEquals(sortB, func.resultSort());

        FuncDecl domainPred = (FuncDecl) theory.functionDeclarations().tail().head();
        assertEquals(1, domainPred.arity());
        assertEquals(sortA, domainPred.argSorts().head());
        assertEquals(Sort.Bool(), domainPred.resultSort());

        Var x = Term.mkVar("x0_0");
        Term expectedAxiom = Term.mkForall(x.of(sortA), Term.mkImp(
                Term.mkApp("inDomain_0", x),
                Term.mkApp("inB", Term.mkApp(func.name(), x))));
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_arity2() {
        // test translating "sig A { f: B->one C }" leads to:
        // - function f: sort(A) x sort(B) -> sort(C)
        // - axiom "forall x1: sort(A), x2: sort(B) . inA(x1) && inB(x2) => inC(f(x1,x2))
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.PrimSig sigC = new Sig.PrimSig("C");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(sigC)).thenReturn(sortC);
        Sig.Field field = sigA.addField("f", sigB.any_arrow_one(sigC));

        // even when lone opt is on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inC", sigC));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        // should have one function and one axiom
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl func = theory.functionDeclarations().head();
        assertEquals(2, func.arity());
        assertEquals(sortA, func.argSorts().head());
        assertEquals(sortB, func.argSorts().tail().head());
        assertEquals(sortC, func.resultSort());

        Var x1 = Term.mkVar("x0_0");
        Var x2 = Term.mkVar("x1_0");
        Term expectedAxiom = Term.mkForall(Arrays.asList(x1.of(sortA), x2.of(sortB)), Term.mkImp(
                Term.mkAnd(Term.mkApp("inA", x1), Term.mkApp("inB", x2)),
                Term.mkApp("inC", Term.mkApp(func.name(), x1, x2))));
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_withThis() {
        // test "sig A { f: A, g: f }" translates properly
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        Sig.Field fieldF = sigA.addField("f", sigA.oneOf());
        Sig.Field fieldG = sigA.addField("g", ExprVar.make(null, "this", Type.make(sigA)).join(fieldF).oneOf());

        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(ctx -> {
                    Expr argExpr = ctx.getArgument(0);
                    assertTrue(argExpr instanceof ExprElementOf);
                    ExprElementOf elementOf = (ExprElementOf) argExpr;
                    assertTrue(elementOf.sub instanceof ExprBinary);
                    ExprBinary join = (ExprBinary) elementOf.sub;
                    assertEquals(ExprBinary.Op.JOIN, join.op);
                    assertTrue(join.left instanceof ExprVar);
                    assertEquals("this", ((ExprVar) join.left).label);
                    assertTrue(join.right instanceof Sig.Field);
                    return Term.mkApp(((Sig.Field) join.right).label, elementOf.tuple.getTerms());
                });

        Term resultG = translator.translate(fieldG, context);
        assertNotNull(resultG); // opt applied

        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl funcG = theory.functionDeclarations().head();
        assertEquals(1, funcG.arity());
        assertEquals(sortA, funcG.argSorts().head());
        assertEquals(sortA, funcG.resultSort());

        Var x = Term.mkVar("x0_0");
        Term expectedAxiom = Term.mkForall(x.of(sortA), Term.mkImp(
                Term.mkApp("inA", x),
                Term.mkApp("f", Term.mkApp(funcG.name(), x))));
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_intJoin() {
        // test [[x.y]] := guard => scalar else 0 where castToScalar(x.y) = (scalar, guard)
        ExprVar x = ExprVar.make(null, "x");
        ExprVar y = ExprVar.make(null, "y");
        Var guard = Term.mkVar("guard");
        Var scalar = Term.mkVar("scalar");
        //noinspection SuspiciousNameCombination
        when(mockScalarCaster.castToScalar(argThat(isSameAs(x.join(y))), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(scalar.of(Sort.Int())), guard));

        Translator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(x.join(y), context);

        Term expected = Term.mkIfThenElse(guard, scalar, IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testCastToScalar_join() {
        // test castToScalar(x.f) = (f(t), guardT && inA(t)) where castToScalar(x) = (t, guardT) and sig A { f: one A }
        ExprVar x = ExprVar.make(null, "x");
        Term flagX = Term.mkVar("t");
        Term guardFlagX = Term.mkVar("guardT");
        when(mockScalarCaster.castToScalar(eq(x), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(flagX, sortA, new ArrayList<>()), guardFlagX));

        Sig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA));
        Sig.Field f = sigA.addField("f", sigA);

        // put the field in the system and get the generated function name
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        assertNotNull(translator.translate(f, context));
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        FuncDecl func = theory.functionDeclarations().head();

        Pair<AnnotatedTerm, Term> result = translator.castToScalar(x.join(f), context);
        assertNotNull(result);
        assertEquals(Term.mkApp(func.name(), flagX), result.a.getTerm());
        assertEquals(sortA, result.a.getSort());
        assertTrue(result.a.getFreeVars().isEmpty());
        assertEquals(Term.mkAnd(guardFlagX, Term.mkApp("inA", flagX)), result.b);
    }

    @Test
    public void testEvaluate_notOptimized() {
        // test that evaluating a field we haven't optimized returns null
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        Sig.Field fieldF = sigA.addField("f", sigA.oneOf());
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        FortressSolution solution = mock(FortressSolution.class);
        assertNull(translator.evaluate(fieldF, solution, context));
    }

    @Test
    public void testEvaluate_domainPred() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.loneOf());

        // lone opt must be on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Value atom1 = Term.mkDomainElement(1, sortA);
        Value atom2 = Term.mkDomainElement(2, sortA);
        FortressSolution solution = mock(FortressSolution.class);
        when(solution.functionPreimage(FuncDecl.mkFuncDecl("inDomain_0", sortA, Sort.Bool()), Term.mkTop()))
                .thenReturn(ValueTupleSet.atoms(atom1, atom2));
        when(solution.evaluateTerm(Term.mkApp("f_0", atom1))).thenReturn(atom2);
        when(solution.evaluateTerm(Term.mkApp("f_0", atom2))).thenReturn(atom1);

        ValueTupleSet actual = translator.evaluate(field, solution, context);
        ValueTupleSet expected = ValueTupleSet.singleton(atom1, atom2).union(ValueTupleSet.singleton(atom2, atom1));
        assertEquals(expected, actual);
    }

    @Test
    public void testEvaluate_empty() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        FortressSolution solution = mock(FortressSolution.class);
        when(mockEvaluator.evaluate(sigA, solution, context)).thenReturn(ValueTupleSet.empty(1));

        ValueTupleSet actual = translator.evaluate(field, solution, context);
        assertTrue(actual.isEmpty());
    }

    @Test
    public void testEvaluate_singletonDomain() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Value domainAtom = Term.mkDomainElement(1, sortA);
        Value rangeAtom = Term.mkDomainElement(1, sortB);
        FortressSolution solution = mock(FortressSolution.class);
        when(mockEvaluator.evaluate(sigA, solution, context)).thenReturn(ValueTupleSet.singleton(domainAtom));
        when(solution.evaluateTerm(Term.mkApp("f_0", domainAtom))).thenReturn(rangeAtom);

        ValueTupleSet actual = translator.evaluate(field, solution, context);
        ValueTupleSet expected = ValueTupleSet.singleton(domainAtom, rangeAtom);
        assertEquals(expected, actual);
    }

    @Test
    public void testEvaluate_twoInDomain() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Value domainAtom1 = Term.mkDomainElement(1, sortA);
        Value domainAtom2 = Term.mkDomainElement(2, sortA);
        Value rangeAtom1 = Term.mkDomainElement(1, sortB);
        Value rangeAtom2 = Term.mkDomainElement(2, sortB);
        FortressSolution solution = mock(FortressSolution.class);
        when(mockEvaluator.evaluate(sigA, solution, context))
                .thenReturn(ValueTupleSet.atoms(domainAtom1, domainAtom2));
        when(solution.evaluateTerm(Term.mkApp("f_0", domainAtom1))).thenReturn(rangeAtom1);
        when(solution.evaluateTerm(Term.mkApp("f_0", domainAtom2))).thenReturn(rangeAtom2);

        ValueTupleSet actual = translator.evaluate(field, solution, context);
        ValueTupleSet expected = ValueTupleSet.singleton(domainAtom1, rangeAtom1)
                .union(ValueTupleSet.singleton(domainAtom2, rangeAtom2));
        assertEquals(expected, actual);
    }

    @Test
    public void testEvaluate_arityThreeWithThis() {
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.PrimSig sigC = new Sig.PrimSig("C");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(sigC)).thenReturn(sortC);
        Sig.Field field = sigA.addField("f", sigB.any_arrow_one(sigC));

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockScalarCaster, mockEvaluator, mockSortPolicy, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inC", sigC));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Value domainAtom1 = Term.mkDomainElement(1, sortA);
        Value domainAtom2 = Term.mkDomainElement(2, sortA);
        Value domain2Atom1 = Term.mkDomainElement(1, sortB);
        Value domain2Atom2 = Term.mkDomainElement(2, sortB);
        Value rangeAtom1 = Term.mkDomainElement(1, sortC);
        Value rangeAtom2 = Term.mkDomainElement(2, sortC);
        FortressSolution solution = mock(FortressSolution.class);
        when(mockEvaluator.evaluate(sigA, solution, context))
                .thenReturn(ValueTupleSet.atoms(domainAtom1, domainAtom2));
        when(mockEvaluator.evaluate(sigB, solution, context)).then(ctx -> {
            // "this" has to be mapped to domainAtom1 first
            TranslationContext innerContext = ctx.getArgument(2);
            assertTrue(innerContext.hasTermMapping("this"));
            assertEquals(sortA, innerContext.getTermMapping("this").getSort());
            assertEquals(domainAtom1, innerContext.getTermMapping("this").getTerm());
            return ValueTupleSet.singleton(domain2Atom1);
        }).then(ctx -> {
            // then mapped to domainAtom2
            TranslationContext innerContext = ctx.getArgument(2);
            assertTrue(innerContext.hasTermMapping("this"));
            assertEquals(sortA, innerContext.getTermMapping("this").getSort());
            assertEquals(domainAtom2, innerContext.getTermMapping("this").getTerm());
            return ValueTupleSet.singleton(domain2Atom2);
        });
        when(solution.evaluateTerm(Term.mkApp("f_0", domainAtom1, domain2Atom1))).thenReturn(rangeAtom1);
        when(solution.evaluateTerm(Term.mkApp("f_0", domainAtom2, domain2Atom2))).thenReturn(rangeAtom2);

        ValueTupleSet actual = translator.evaluate(field, solution, context);
        ValueTupleSet expected = ValueTupleSet.singleton(domainAtom1, domain2Atom1, rangeAtom1)
                .union(ValueTupleSet.singleton(domainAtom2, domain2Atom2, rangeAtom2));
        assertEquals(expected, actual);
    }

}
