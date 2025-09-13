package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;

import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class FunctionOptTranslatorTest {

    // Some test sorts
    private final Sort sortA = Sort.mkSortConst("sortA");
    private final Sort sortB = Sort.mkSortConst("sortB");
    private final Sort sortC = Sort.mkSortConst("sortC");

    private Translator mockRoot;
    private Evaluator mockEvaluator;

    private SortPolicy mockSortPolicy;
    private SigAxioms sigAxioms;
    private NameGenerator nameGenerator;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockEvaluator = mock(Evaluator.class);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(
                Theory.empty().withSort(sortA).withSort(sortB).withSort(sortC).withSort(Sort.Int()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(mock(ModelInfo.class), new ArrayList<>(), mockSortPolicy, mockScoper));
        nameGenerator = new SanitizingNameGenerator();
        sigAxioms = new SigAxioms(mockRoot, mockSortPolicy, nameGenerator);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_inapplicable() {
        // test "sig A { f: set B }" doesn't apply the opt
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.setOf());
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_lone_inapplicable() {
        // test "sig A { f: lone B }" doesn't apply the opt when it's off
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.loneOf());
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, false);
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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var x0 = Term.mkVar("x_0");
        Var x1 = Term.mkVar("x_1");
        Term expectedAxiom = Term.mkAnd(
                Term.mkForall(Arrays.asList(x0.of(sortA), x1.of(sortB)), Term.mkImp(domainAxiom1, domainAxiom2)),
                rangeAxiom);
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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // lone opt must be on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        // should have two functions and two axioms
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

        Var x0 = Term.mkVar("x_0");
        Var x1 = Term.mkVar("x_1");
        Term expectedAxiom = Term.mkAnd(
                Term.mkForall(Arrays.asList(x0.of(sortA), x1.of(sortB)), Term.mkImp(domainAxiom1, domainAxiom2)),
                rangeAxiom);
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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var x0 = Term.mkVar("x_0");
        Var x1 = Term.mkVar("x_1");
        Var x2 = Term.mkVar("x_2");
        Term expectedAxiom = Term.mkAnd(
                Term.mkForall(Arrays.asList(x0.of(sortA), x1.of(sortB), x2.of(sortC)),
                        Term.mkImp(domainAxiom1, domainAxiom2)),
                rangeAxiom);
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_withThis() {
        // test "sig A { f: A, g: f }" translates properly
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        Sig.Field fieldF = sigA.addField("f", sigA.oneOf());
        Sig.Field fieldG = sigA.addField("g", ExprVar.make(null, "this", Type.make(sigA)).join(fieldF).oneOf());

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        Translator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term resultG = translator.translate(fieldG, context);
        assertNotNull(resultG); // opt applied

        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl funcG = theory.functionDeclarations().head();
        assertEquals(1, funcG.arity());
        assertEquals(sortA, funcG.argSorts().head());
        assertEquals(sortA, funcG.resultSort());

        Var x0 = Term.mkVar("x_0");
        Var x1 = Term.mkVar("x_1");
        Term expectedAxiom = Term.mkAnd(
                Term.mkForall(Arrays.asList(x0.of(sortA), x1.of(sortA)),
                        Term.mkImp(domainAxiom1, domainAxiom2)),
                rangeAxiom);
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testCastToScalar_unary_one() {
        // test "sig A { f: B }" results in a scalar function f: sort(A)->sort(B) with the appropriate guard
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Scalar scalar = translator.castToScalar(field, context);
        assertNotNull(scalar);

        Var x = Term.mkVar("x");
        context.addFortressVar(x.of(sortA));
        assertFalse(scalar.isNilary());
        assertEquals(1, scalar.getArity());
        assertEquals(sortB, scalar.getResultSort());
        assertEquals(Term.mkApp("f_0", x), scalar.getScalar(TermTuple.fromVars(x.of(sortA)), context));
        assertEquals(domainAxiom2, scalar.getGuard(TermTuple.fromVars(x.of(sortA)), context));
    }

    @Test
    public void testCastToScalar_unary_lone() {
        // test "sig A { f: lone B }" results in a scalar function f: sort(A)->sort(B) with the appropriate guard
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.loneOf());

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Scalar scalar = translator.castToScalar(field, context);
        assertNotNull(scalar);

        Var x = Term.mkVar("x");
        context.addFortressVar(x.of(sortA));
        assertFalse(scalar.isNilary());
        assertEquals(1, scalar.getArity());
        assertEquals(sortB, scalar.getResultSort());
        assertEquals(Term.mkApp("f_0", x), scalar.getScalar(TermTuple.fromVars(x.of(sortA)), context));
        assertEquals(Term.mkApp("inDomain_0", x), scalar.getGuard(TermTuple.fromVars(x.of(sortA)), context));
    }

    @Test
    public void testCastToScalar_binary_one() {
        // test "sig A { f: B->one C }" results in a scalar function f: sort(A) x sort(B) -> sort(C) with guard
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.PrimSig sigC = new Sig.PrimSig("C");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(sigC)).thenReturn(sortC);
        Sig.Field field = sigA.addField("f", sigB.any_arrow_one(sigC));

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Scalar scalar = translator.castToScalar(field, context);
        assertNotNull(scalar);

        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        context.addFortressVars(x.of(sortA), y.of(sortB));
        assertFalse(scalar.isNilary());
        assertEquals(2, scalar.getArity());
        assertEquals(sortC, scalar.getResultSort());
        assertEquals(Term.mkApp("f_0", x, y), scalar.getScalar(TermTuple.fromVars(x.of(sortA), y.of(sortB)), context));
        assertEquals(Term.mkAnd(domainAxiom2, domainAxiom2),
                scalar.getGuard(TermTuple.fromVars(x.of(sortA), y.of(sortB)), context));
    }

    @Test
    public void testCastToScalar_binary_lone() {
        // test "sig A { f: B->lone C }" results in a scalar function f: sort(A) x sort(B) -> sort(C) with guard
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.PrimSig sigC = new Sig.PrimSig("C");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(sigC)).thenReturn(sortC);
        Sig.Field field = sigA.addField("f", sigB.any_arrow_lone(sigC));

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // even when lone opt is on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        Scalar scalar = translator.castToScalar(field, context);
        assertNotNull(scalar);

        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        context.addFortressVars(x.of(sortA), y.of(sortB));
        assertFalse(scalar.isNilary());
        assertEquals(2, scalar.getArity());
        assertEquals(sortC, scalar.getResultSort());
        assertEquals(Term.mkApp("f_0", x, y), scalar.getScalar(TermTuple.fromVars(x.of(sortA), y.of(sortB)), context));
        assertEquals(Term.mkApp("inDomain_0", x, y), scalar.getGuard(
                TermTuple.fromVars(x.of(sortA), y.of(sortB)), context));
    }

    @Test
    public void testEvaluate_notOptimized() {
        // test that evaluating a field we haven't optimized returns null
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        Sig.Field fieldF = sigA.addField("f", sigA.oneOf());
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        // lone opt must be on
        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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

        Var rangeAxiom = Term.mkVar("rangeAxiom");
        Var domainAxiom1 = Term.mkVar("domainAxiom1");
        Var domainAxiom2 = Term.mkVar("domainAxiom2");

        FunctionOptTranslator translator = new FunctionOptTranslator(
                mockRoot, mockEvaluator, mockSortPolicy, sigAxioms, nameGenerator, true);
        when(mockRoot.translate(any(), any()))
                .thenReturn(rangeAxiom)
                .thenReturn(domainAxiom1)
                .thenReturn(domainAxiom2);

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
