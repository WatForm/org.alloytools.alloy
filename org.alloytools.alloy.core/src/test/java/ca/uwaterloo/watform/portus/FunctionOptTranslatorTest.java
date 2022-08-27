package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.FuncDecl;
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
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class FunctionOptTranslatorTest {

    // Some test sorts
    private final Sort sortA = Sort.mkSortConst("sortA");
    private final Sort sortB = Sort.mkSortConst("sortB");

    private Translator mockRoot;

    private SortPolicy mockSortPolicy;
    private TranslationContext context;

    // For use in Mockito then() with a translate() call: map (x1,...,xn) \in expr to funcName(x1,...,xn)
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
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(sortA).withSort(sortB));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new FortressOptions(), mockScoper, mockSortPolicy);
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

        Translator translator = new FunctionOptTranslator(mockRoot, false);
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

}
