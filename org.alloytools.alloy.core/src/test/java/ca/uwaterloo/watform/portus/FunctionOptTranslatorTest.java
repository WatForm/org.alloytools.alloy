package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;

import java.util.ArrayList;

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
                Theory.empty().withSort(sortA).withSort(sortB).withSort(Sort.Int()));
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_inapplicable() {
        // test "sig A { f: set B }" doesn't apply the opt
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.setOf());
        Translator translator = new FunctionOptTranslator(mockRoot, mockScalarCaster, mockEvaluator, true);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_lone_inapplicable() {
        // test "sig A { f: lone B }" doesn't apply the opt when it's off
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.loneOf());
        Translator translator = new FunctionOptTranslator(mockRoot, mockScalarCaster, mockEvaluator, false);
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
        Translator translator = new FunctionOptTranslator(mockRoot, mockScalarCaster, mockEvaluator, true);
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
    public void testTranslate_intJoin() {
        // test [[x.y]] := guard => scalar else 0 where castToScalar(x.y) = (scalar, guard)
        ExprVar x = ExprVar.make(null, "x");
        ExprVar y = ExprVar.make(null, "y");
        Var guard = Term.mkVar("guard");
        Var scalar = Term.mkVar("scalar");
        //noinspection SuspiciousNameCombination
        when(mockScalarCaster.castToScalar(argThat(isSameAs(x.join(y))), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(scalar.of(Sort.Int())), guard));

        Translator translator = new FunctionOptTranslator(mockRoot, mockScalarCaster, mockEvaluator, true);
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
        FunctionOptTranslator translator = new FunctionOptTranslator(mockRoot, mockScalarCaster, mockEvaluator, true);
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

}
