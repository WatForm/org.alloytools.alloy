package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;

import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class FunctionOptTranslatorTest {

    // Some test sorts
    private final Sort sortA = Sort.mkSortConst("sortA");
    private final Sort sortB = Sort.mkSortConst("sortB");

    private Translator mockRoot;

    private SortPolicy mockSortPolicy;
    private RangeAssigner mockRangeAssigner;
    private TranslationContext context;

    /** For use in Mockito then() with a translate() call: map (x1,...,xn) \in expr to funcName(x1,...,xn). */
    private Answer<Term> useTestFunction(String funcName, Expr expr) {
        return ctx -> {
            Expr argExpr = ctx.getArgument(0);
            assertTrue(argExpr instanceof ExprElementOf);
            ExprElementOf elementOf = (ExprElementOf) argExpr;
            assertEquals(expr, elementOf.sub);
            return Term.mkApp(funcName, elementOf.tuple.getVars());
        };
    }

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(
                Theory.empty().withSort(sortA).withSort(sortB).withSort(Sort.Int()));
        mockRangeAssigner = mock(RangeAssigner.class);
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_inapplicable() {
        // test "sig A { f: set B }" doesn't apply the opt
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.setOf());
        Translator translator = new FunctionOptTranslator(mockRoot, true);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_lone_inapplicable() {
        // test "sig A { f: lone B }" doesn't apply the opt when it's off
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.loneOf());
        Translator translator = new FunctionOptTranslator(mockRoot, false);
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

        Translator translator = new FunctionOptTranslator(mockRoot, true); // even when lone opt is on
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
    public void testTranslate_intJoin_boundVar() {
        // test [[x.y]] := (true & inA(x)) => y(x) else 0 with "sig A {y: Int}"
        // the redundant true comes from conveniences in FunctionOptTranslator
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        Sig.Field intField = sigA.addField("y", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA));

        // put it in the system and get the generated function name
        assertNotNull(translator.translate(intField, context));
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        FuncDecl func = theory.functionDeclarations().head();

        AnnotatedVar x = Term.mkVar("x").of(sortA);
        context.addVarMapping("x", x);
        ExprHasName alloyVar = sigA.oneOf("x").names.get(0);
        Term result = translator.translate(alloyVar.join(intField), context);

        Term expected = Term.mkIfThenElse(
                Term.mkAnd(Term.mkTop(), Term.mkApp("inA", x.variable())),
                Term.mkApp(func.name(), x.variable()),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_intJoin_oneSig() {
        // test [[A.y]] := (true & inA(@1)) => y(@1) else 0 with "one sig A {y: Int}", where @1 is the domain element
        // of sort(A), and the redundant true comes from conveniences in FunctionOptTranslator
        // could be optimized better by a proper one sig optimization, but eh
        Sig.PrimSig sigA = new Sig.PrimSig("A", Attr.ONE);
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any())).thenReturn(new Pair<>(1, 1));
        Sig.Field intField = sigA.addField("y", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA));

        // put it in the system and get the generated function name
        assertNotNull(translator.translate(intField, context));
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        FuncDecl func = theory.functionDeclarations().head();

        Term result = translator.translate(sigA.join(intField), context);
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(Term.mkTop(), Term.mkApp("inA", Term.mkDomainElement(1, sortA))),
                Term.mkApp(func.name(), Term.mkDomainElement(1, sortA)),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_intJoin_twoJoins() {
        // test [[x.y.z]] := ((true & inA(x)) & inB(y(x))) => z(y(x)) else 0
        // with sig A { y: B } and sig B { z: Int }
        // again, the redundant true comes from conveniences in FunctionOptTranslator
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        Sig.Field fieldY = sigA.addField("y", sigB);
        Sig.Field fieldZ = sigB.addField("z", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        // put the fields in the system and get the generated function names
        assertNotNull(translator.translate(fieldY, context));
        assertNotNull(translator.translate(fieldZ, context));
        Theory theory = context.getTheory();
        assertEquals(2, theory.functionDeclarations().size());
        FuncDecl funcY = theory.functionDeclarations().head();
        FuncDecl funcZ = theory.functionDeclarations().last();

        AnnotatedVar x = Term.mkVar("x").of(sortA);
        context.addVarMapping("x", x);
        ExprHasName alloyVar = sigA.oneOf("x").names.get(0);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyVar.join(fieldY).join(fieldZ), context);

        Term expected = Term.mkIfThenElse(
                Term.mkAnd(
                        Term.mkAnd(Term.mkTop(), Term.mkApp("inA", x.variable())),
                        Term.mkApp("inB", Term.mkApp(funcY.name(), x.variable()))),
                Term.mkApp(funcZ.name(), Term.mkApp(funcY.name(), x.variable())),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

}
