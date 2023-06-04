package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.DomainElement;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import scala.jdk.javaapi.CollectionConverters;

import java.util.Arrays;
import java.util.Set;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class OrderingModuleOptTranslatorTest {

    private RangeAssigner rangeAssigner;
    private ScopeComputer scoper;
    private TranslationContext context;
    private SortPolicy policy;
    private ScalarCaster scalarCaster;
    private OrderingModuleOptTranslator translator;

    // "Ord" from the ordering module, with a pred/totalorder fact
    private Sig.PrimSig ordSig;
    private Sig.Field firstField;
    private Sig.Field nextField;
    private Sig.PrimSig orderedSig; // the sig being ordered
    private Sort orderedSigSort; // its sort

    @Before
    public void setUp() {
        orderedSig = new Sig.PrimSig("Ordered");
        orderedSigSort = Sort.mkSortConst("OrderedSort");
        ordSig = new Sig.PrimSig("Ord", Attr.ONE);
        Sort ordSigSort = Sort.mkSortConst("OrdSort");
        firstField = ordSig.addField("First", orderedSig.setOf());
        nextField = ordSig.addField("Next", orderedSig.product(orderedSig));

        policy = mock(SortPolicy.class);
        rangeAssigner = mock(RangeAssigner.class, withSettings()
                .useConstructor(Arrays.asList(ordSig, orderedSig)));
        scoper = mock(ScopeComputer.class);
        scalarCaster = mock(ScalarCaster.class);
        translator = new OrderingModuleOptTranslator((expr, context) -> {
            // recursive calls should check membership in orderedSig, translate as inOrderedSig(x)
            if (!(expr instanceof ExprElementOf)) fail();
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            if (exprElementOf.sub != orderedSig) fail();
            if (exprElementOf.tuple.size() != 1 || exprElementOf.tuple.getSort(0) != orderedSigSort) fail();
            return Term.mkApp("inOrderedSig", exprElementOf.tuple.getTerm(0));
        }, scalarCaster, policy);

        when(scoper.isExact(orderedSig)).thenReturn(true);
        when(policy.getSort(orderedSig)).thenReturn(orderedSigSort);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(orderedSigSort).withSort(ordSigSort));
        when(policy.getSort(ordSig)).thenReturn(ordSigSort);
        when(rangeAssigner.getDomainElementRange(eq(ordSig), any(), any())).thenReturn(new Pair<>(1, 1));
        ordSig.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                orderedSig, ordSig.join(firstField), ordSig.join(nextField))));

        context = new TranslationContext(new PortusOptions(), scoper, policy, rangeAssigner);
    }

    @Test
    public void testTranslate_orderedSig_notLazy() {
        // nothing translated, but next is still added
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        // there should be two axioms
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(1, orderedSigSort)),
                        DomainElement.apply(2, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(2, orderedSigSort)),
                        DomainElement.apply(3, orderedSigSort))));

        // the range axiom should also be generated eagerly
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_first_simple() {
        // first is hardcoded as the first DE in the range: [[x \in first]] := x = @_(first)
        // now this is failing?????
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(orderedSigSort)), ordSig.join(firstField)), context);
        assertEquals(Term.mkEq(x, DomainElement.apply(1, orderedSigSort)), result);
    }

    @Test
    public void testTranslate_orderedSig_first_notDE1() {
        // first is hardcoded as the first DE in the range: [[x \in first]] := x = @_(first)
        when(scoper.sig2scope(orderedSig)).thenReturn(10);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(5, 10));
        translator.translate(ordSig, context);
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(orderedSigSort)), ordSig.join(firstField)), context);
        assertEquals(Term.mkEq(x, DomainElement.apply(5, orderedSigSort)), result);
    }

    @Test
    public void testTranslate_orderedSig_next() {
        // a bunch of axioms are added for next:
        // next(@_1) = @_2, next(@_2) = @_3, but next(@_3) is left undefined
        // and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_3) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(orderedSigSort), y.of(orderedSigSort)),
                ordSig.join(nextField)), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        // there should be the two axioms listed above
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(1, orderedSigSort)),
                        DomainElement.apply(2, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(2, orderedSigSort)),
                        DomainElement.apply(3, orderedSigSort))));

        // check that [[(x,y) \in next]] translated correctly
        Term expected = Term.mkAnd(
                Term.mkAnd(
                        Term.mkApp("inOrderedSig", x),
                        Term.mkNot(Term.mkEq(x, DomainElement.apply(3, orderedSigSort)))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);

        // we have the range axiom
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_notStartingAtDE1() {
        // when we use next, a bunch of axioms get added: with scope 4, offset 3,
        // next(@_3) = @_4, next(@_4) = @_5, next(@_5) = @_6, but next(@_6) is left undefined
        // and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_6) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(4);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(3, 6));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(orderedSigSort), y.of(orderedSigSort)),
                ordSig.join(nextField)), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        // there should be the three axioms listed above
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(3, orderedSigSort)),
                        DomainElement.apply(4, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(4, orderedSigSort)),
                        DomainElement.apply(5, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), DomainElement.apply(5, orderedSigSort)),
                        DomainElement.apply(6, orderedSigSort))));

        // check that [[(x,y) \in next]] translated correctly
        Term expected = Term.mkAnd(
                Term.mkAnd(
                        Term.mkApp("inOrderedSig", x),
                        Term.mkNot(Term.mkEq(x, DomainElement.apply(6, orderedSigSort)))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);

        // we have the range axiom
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_scope1() {
        // edge case: what happens when the scope is 1?
        // no axioms and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_1) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(1);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 1));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(orderedSigSort), y.of(orderedSigSort)),
                ordSig.join(nextField)), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        // there should be no axioms
        assertEquals(0, context.getTheory().axioms().size());

        // check that [[(x,y) \in next]] translated correctly
        Term expected = Term.mkAnd(
                Term.mkAnd(
                        Term.mkApp("inOrderedSig", x),
                        Term.mkNot(Term.mkEq(x, DomainElement.apply(1, orderedSigSort)))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);

        // we have the range axiom
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any(), any());
    }

    @Test
    public void testCastToScalar_first() {
        // test castToScalar(Ord.first) = (@1: Int, Top)
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Pair<AnnotatedTerm, Term> scalar = translator.castToScalar(ordSig.join(firstField), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        assertNotNull(scalar);
        assertEquals(DomainElement.apply(1, orderedSigSort), scalar.a.getTerm());
        assertEquals(orderedSigSort, scalar.a.getSort());
        assertTrue(scalar.a.getFreeVars().isEmpty());
        assertEquals(Term.mkTop(), scalar.b);
    }

    @Test
    public void testCastToScalar_next() {
        // test castToScalar(x.(Ord.next)) = (next(x): Sort, guardX && (inOrderedSig(x) && x != @last))
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        ExprVar alloyX = ExprVar.make(null, "x");
        Var x = Term.mkVar("x");
        Var guardX = Term.mkVar("guardX");
        when(scalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(orderedSigSort)), guardX));

        Pair<AnnotatedTerm, Term> scalar = translator.castToScalar(alloyX.join(ordSig.join(nextField)), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        assertNotNull(scalar);
        assertEquals(Term.mkApp(nextFunc.name(), x), scalar.a.getTerm());
        assertEquals(orderedSigSort, scalar.a.getSort());
        assertTrue(scalar.a.getFreeVars().isEmpty());

        Term expectedGuard = Term.mkAnd(guardX, Term.mkAnd(
                Term.mkApp("inOrderedSig", x),
                Term.mkNot(Term.mkEq(x, Term.mkDomainElement(3, orderedSigSort)))));
        assertEquals(expectedGuard, scalar.b);
    }

    @Test
    public void testCastToScalar_nextWithNoops() {
        // test castToScalar(x.NOOP(Ord.next)) = (next(x): Sort, guardX && (inOrderedSig(x) && x != @last))
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig, policy, context)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        ExprVar alloyX = ExprVar.make(null, "x");
        Var x = Term.mkVar("x");
        Var guardX = Term.mkVar("guardX");
        when(scalarCaster.castToScalar(eq(alloyX), any()))
                .thenReturn(new Pair<>(new AnnotatedTerm(x.of(orderedSigSort)), guardX));

        Expr rhs = ExprUnary.Op.NOOP.make(null, ExprUnary.Op.NOOP.make(null, ordSig).cast2int()
                .join(nextField.cast2int().cast2sigint()).cast2int());
        Pair<AnnotatedTerm, Term> scalar = translator.castToScalar(alloyX.join(rhs), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        assertNotNull(scalar);
        assertEquals(Term.mkApp(nextFunc.name(), x), scalar.a.getTerm());
        assertEquals(orderedSigSort, scalar.a.getSort());
        assertTrue(scalar.a.getFreeVars().isEmpty());

        Term expectedGuard = Term.mkAnd(guardX, Term.mkAnd(
                Term.mkApp("inOrderedSig", x),
                Term.mkNot(Term.mkEq(x, Term.mkDomainElement(3, orderedSigSort)))));
        assertEquals(expectedGuard, scalar.b);
    }

}
