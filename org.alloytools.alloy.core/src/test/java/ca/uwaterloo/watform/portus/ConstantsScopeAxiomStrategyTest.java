package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class ConstantsScopeAxiomStrategyTest {

    private Sig testSig;
    private Sort testSort;

    private Translator mockTranslator;
    private SortPolicy mockSortPolicy;
    private TranslationContext context;

    private ConstantsScopeAxiomStrategy strategy;

    private Answer<Term> useSigPredicate(Sig sig, @SuppressWarnings("SameParameterValue") String predName) {
        return ctx -> {
            Expr expr = ctx.getArgument(0);
            expr = expr.deNOP();

            boolean negated = expr instanceof ExprUnary;
            if (negated) {
                // Must be wrapped in a NOT
                assertEquals(ExprUnary.Op.NOT, ((ExprUnary) expr).op);
                expr = ((ExprUnary) expr).sub;
            }

            // Must be an ExprElementOf(v, sig)
            assertTrue(expr instanceof ExprElementOf);
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            assertEquals(sig, exprElementOf.sub);
            assertEquals(1, exprElementOf.tuple.size());

            // Return predName(v), and negate it if we were negated
            Term app = Term.mkApp(predName, exprElementOf.tuple.getTerm(0));
            return negated ? Term.mkNot(app) : app;
        };
    }

    @Before
    public void setUp() {
        testSig = new Sig.PrimSig("Sig");
        testSort = Sort.mkSortConst("Sort");

        mockTranslator = mock(Translator.class);
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(testSort));
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);

        strategy = new ConstantsScopeAxiomStrategy(mockSortPolicy);
    }

    @Test
    public void testNonExactScopeAxiom_scope1_sortScope3() {
        // Simple case: two distinct constants, no special cases
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(3);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeNonExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have 2 constants asserted to be not in sig
        assertEquals(2, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant1 = context.getTheory().constantDeclarations().head();
        AnnotatedVar constant2 = (AnnotatedVar) context.getTheory().constantDeclarations().tail().head();
        assertEquals(testSort, constant1.sort());
        assertEquals(testSort, constant2.sort());

        Term expectedAxiom = Term.mkAnd(
                Term.mkNot(Term.mkApp("sig", constant1.variable())),
                Term.mkNot(Term.mkApp("sig", constant2.variable())),
                Term.mkDistinct(constant1.variable(), constant2.variable()));
        assertEquals(expectedAxiom, axiom);
    }

    @Test
    public void testNonExactScopeAxiom_scope1_sortScope2() {
        // Only one constant, so no distinct
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(2);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeNonExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have 1 constant asserted to be not in sig
        assertEquals(1, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant = context.getTheory().constantDeclarations().head();
        assertEquals(testSort, constant.sort());

        // no distinct because it doesn't make sense for 1 constant
        Term expectedAxiom = Term.mkAnd(
                Term.mkNot(Term.mkApp("sig", constant.variable())));
        assertEquals(expectedAxiom, axiom);
    }

    @Test
    public void testNonExactScopeAxiom_scope1_sortScope1() {
        // No constants or axiom at all!
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(1);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeNonExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have no constants, and the axiom should just be true
        assertEquals(0, context.getTheory().constantDeclarations().size());
        assertEquals(Term.mkTop(), axiom);
    }

    @Test
    public void testExactScopeAxiom_scope1_sortScope3() {
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(3);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have 3 constants: 2 asserted not in sig, 1 asserted in sig
        assertEquals(3, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant1 = context.getTheory().constantDeclarations().head();
        AnnotatedVar constant2 = (AnnotatedVar) context.getTheory().constantDeclarations().tail().head();
        AnnotatedVar constant3 = (AnnotatedVar) ((scala.collection.Set<AnnotatedVar>)
                context.getTheory().constantDeclarations().tail().tail()).head();
        assertEquals(testSort, constant1.sort());
        assertEquals(testSort, constant2.sort());
        assertEquals(testSort, constant3.sort());

        Term expectedAxiom = Term.mkAnd(
                Term.mkAnd(
                        Term.mkNot(Term.mkApp("sig", constant1.variable())),
                        Term.mkNot(Term.mkApp("sig", constant2.variable())),
                        Term.mkDistinct(constant1.variable(), constant2.variable())),
                Term.mkApp("sig", constant3.variable()));
        assertEquals(expectedAxiom, axiom);
    }

    @Test
    public void testExactScopeAxiom_scope2_sortScope3() {
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(3);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeExactScopeAxiom(testSig, 2, mockTranslator, context);

        // should have 3 constants: 1 asserted not in sig, 2 asserted in sig
        assertEquals(3, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant1 = context.getTheory().constantDeclarations().head();
        AnnotatedVar constant2 = (AnnotatedVar) context.getTheory().constantDeclarations().tail().head();
        AnnotatedVar constant3 = (AnnotatedVar) ((scala.collection.Set<AnnotatedVar>)
                context.getTheory().constantDeclarations().tail().tail()).head();
        assertEquals(testSort, constant1.sort());
        assertEquals(testSort, constant2.sort());
        assertEquals(testSort, constant3.sort());

        Term expectedAxiom = Term.mkAnd(
                Term.mkNot(Term.mkApp("sig", constant1.variable())),
                Term.mkAnd(
                        Term.mkApp("sig", constant2.variable()),
                        Term.mkApp("sig", constant3.variable()),
                        Term.mkDistinct(constant2.variable(), constant3.variable())));
        assertEquals(expectedAxiom, axiom);
    }

    @Test
    public void testExactScopeAxiom_scope1_sortScope2() {
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(2);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have 2 constants: 1 asserted not in sig, 1 asserted in sig
        assertEquals(2, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant1 = context.getTheory().constantDeclarations().head();
        AnnotatedVar constant2 = (AnnotatedVar) context.getTheory().constantDeclarations().tail().head();
        assertEquals(testSort, constant1.sort());
        assertEquals(testSort, constant2.sort());

        Term expectedAxiom = Term.mkAnd(
                Term.mkNot(Term.mkApp("sig", constant1.variable())),
                Term.mkApp("sig", constant2.variable()));
        assertEquals(expectedAxiom, axiom);
    }

    @Test
    public void testExactScopeAxiom_scope1_sortScope1() {
        when(mockSortPolicy.getSort(testSig)).thenReturn(testSort);
        when(mockSortPolicy.getSortScope(testSort)).thenReturn(1);
        when(mockTranslator.translate(any(), any())).then(useSigPredicate(testSig, "sig"));

        Term axiom = strategy.makeExactScopeAxiom(testSig, 1, mockTranslator, context);

        // should have 1 constant asserted to be in sig
        assertEquals(1, context.getTheory().constantDeclarations().size());
        AnnotatedVar constant = context.getTheory().constantDeclarations().head();
        assertEquals(testSort, constant.sort());

        Term expectedAxiom = Term.mkAnd(
                Term.mkTop(),
                Term.mkApp("sig", constant.variable()));
        assertEquals(expectedAxiom, axiom);
    }

}
