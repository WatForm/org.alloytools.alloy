package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.ExprList;
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
import static org.junit.Assert.fail;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class OrderingModuleOptTranslatorTest {

    private SortPolicy policy;
    private ScopeComputer scoper;
    private TranslationContext context;
    private Translator translator;

    // "Ord" from the ordering module, with a pred/totalorder fact
    private Sig.PrimSig ordSig;
    private Sig.Field firstField;
    private Sig.Field nextField;
    private Sig.PrimSig orderedSig; // the sig being ordered
    private Sort orderedSigSort; // its sort

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class);
        scoper = mock(ScopeComputer.class);
        translator = new OrderingModuleOptTranslator((expr, ctx) -> {
            // we don't expect this translator to recurse at all
            fail("No recursive calls expected!");
            return null;
        });

        orderedSig = new Sig.PrimSig("Ordered");
        orderedSigSort = Sort.mkSortConst("OrderedSort");
        when(scoper.isExact(orderedSig)).thenReturn(true);
        when(policy.getSort(orderedSig)).thenReturn(orderedSigSort);
        ordSig = new Sig.PrimSig("Ord", Attr.ONE);
        Sort ordSigSort = Sort.mkSortConst("OrdSort");
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(orderedSigSort).withSort(ordSigSort));
        when(policy.getSort(ordSig)).thenReturn(ordSigSort);
        when(policy.getDomainElementRange(eq(ordSig), any())).thenReturn(new Pair<>(1, 1));
        firstField = ordSig.addField("First", orderedSig.setOf());
        nextField = ordSig.addField("Next", orderedSig.product(orderedSig));
        ordSig.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                orderedSig, ordSig.join(firstField), ordSig.join(nextField))));

        context = new TranslationContext(new PortusOptions(), scoper, policy);
    }

    @Test
    public void testTranslate_orderedSig_lazy() {
        // nothing is generated before next is translated
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);
        assertEquals(0, context.getTheory().axioms().size());
        assertEquals(0, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_orderedSig_first_simple() {
        // first is hardcoded as the first DE in the range: [[x \in first]] := x = @_(first)
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(
                new VarTuple(x.of(orderedSigSort)), ordSig.join(firstField)), context);
        assertEquals(Term.mkEq(x, DomainElement.apply(1, orderedSigSort)), result);

        // still no next axiom since we didn't use it
        assertEquals(0, context.getTheory().axioms().size());
        assertEquals(0, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_orderedSig_first_notDE1() {
        // first is hardcoded as the first DE in the range: [[x \in first]] := x = @_(first)
        when(scoper.sig2scope(orderedSig)).thenReturn(10);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(5, 10));
        translator.translate(ordSig, context);
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(
                new VarTuple(x.of(orderedSigSort)), ordSig.join(firstField)), context);
        assertEquals(Term.mkEq(x, DomainElement.apply(5, orderedSigSort)), result);

        // still no next axiom since we didn't use it
        assertEquals(0, context.getTheory().axioms().size());
        assertEquals(0, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_orderedSig_next() {
        // when we use next, a bunch of axioms get added: with scope 3,
        // next(@_1) = @_2, next(@_2) = @_3, but next(@_3) is left undefined
        // and [[(x,y) \in next]] := x != @_3 && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                new VarTuple(x.of(orderedSigSort), y.of(orderedSigSort)),
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
                Term.mkNot(Term.mkEq(x, DomainElement.apply(3, orderedSigSort))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_orderedSig_next_notStartingAtDE1() {
        // when we use next, a bunch of axioms get added: with scope 4, offset 3,
        // next(@_3) = @_4, next(@_4) = @_5, next(@_5) = @_6, but next(@_6) is left undefined
        // and [[(x,y) \in next]] := x != @_6 && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(4);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(3, 6));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                new VarTuple(x.of(orderedSigSort), y.of(orderedSigSort)),
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
                Term.mkNot(Term.mkEq(x, DomainElement.apply(6, orderedSigSort))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_orderedSig_next_scope1() {
        // edge case: what happens when the scope is 1?
        // no axioms and [[(x,y) \in next]] := x != @_1 && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(1);
        when(policy.getDomainElementRange(orderedSig, scoper)).thenReturn(new Pair<>(1, 1));
        translator.translate(ordSig, context);

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(ExprElementOf.make(
                new VarTuple(x.of(orderedSigSort), y.of(orderedSigSort)),
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
                Term.mkNot(Term.mkEq(x, DomainElement.apply(1, orderedSigSort))),
                Term.mkEq(Term.mkApp(nextFunc.name(), x), y));
        assertEquals(expected, result);
    }

}
