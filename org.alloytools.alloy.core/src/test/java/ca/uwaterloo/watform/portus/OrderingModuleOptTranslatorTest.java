package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

// TODO: Also test with the definition!
public class OrderingModuleOptTranslatorTest {

    private RangeAssigner rangeAssigner;
    private ScopeComputer scoper;
    private TranslationContext context;
    private OrderingModuleOptTranslator translator;
    private OrderingModuleOptTranslator defnTranslator;

    // "Ord" from the ordering module, with a pred/totalorder fact
    private Sig.PrimSig ordSig;
    private Sig.Field firstField;
    private Sig.Field nextField;
    private Sig.PrimSig orderedSig; // the sig being ordered
    private Sort orderedSigSort; // its sort

    private SortPolicy policy;

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
                .useConstructor(Arrays.asList(ordSig, orderedSig), policy, scoper));
        scoper = mock(ScopeComputer.class);
        Translator recursiveTranslator = (expr, context) -> {
            // recursive calls should check membership in orderedSig, translate as inOrderedSig(x)
            if (!(expr instanceof ExprElementOf)) fail();
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            if (exprElementOf.sub != orderedSig) fail();
            if (exprElementOf.tuple.size() != 1 || exprElementOf.tuple.getSort(0) != orderedSigSort) fail();
            return Term.mkApp("inOrderedSig", exprElementOf.tuple.getTerm(0));
        };
        translator = new OrderingModuleOptTranslator(
                recursiveTranslator, policy, new SanitizingNameGenerator(), false);
        defnTranslator = new OrderingModuleOptTranslator(
                recursiveTranslator, policy, new SanitizingNameGenerator(), true);

        when(scoper.isExact(orderedSig)).thenReturn(true);
        when(policy.getSort(orderedSig)).thenReturn(orderedSigSort);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(orderedSigSort).withSort(ordSigSort));
        when(policy.getSort(ordSig)).thenReturn(ordSigSort);
        when(rangeAssigner.getDomainElementRange(eq(ordSig))).thenReturn(new Pair<>(1, 1));
        ordSig.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                orderedSig, ordSig.join(firstField), ordSig.join(nextField))));

        context = new TranslationContext(new PortusOptions(), scoper, policy, rangeAssigner);
    }

    @Test
    public void testTranslate_orderedSig_notLazy() {
        // nothing translated, but next is still added
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
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
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(1, orderedSigSort)),
                        Term.mkDomainElement(2, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(2, orderedSigSort)),
                        Term.mkDomainElement(3, orderedSigSort))));

        // the range axiom should also be generated eagerly
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next() {
        // a bunch of axioms are added for next:
        // next(@_1) = @_2, next(@_2) = @_3, but next(@_3) is left undefined
        // and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_3) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

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
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(1, orderedSigSort)),
                        Term.mkDomainElement(2, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(2, orderedSigSort)),
                        Term.mkDomainElement(3, orderedSigSort))));

        // we have the range axiom after running the scalar caster
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_notStartingAtDE1() {
        // when we use next, a bunch of axioms get added: with scope 4, offset 3,
        // next(@_3) = @_4, next(@_4) = @_5, next(@_5) = @_6, but next(@_6) is left undefined
        // and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_6) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(4);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(3, 6));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

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
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(3, orderedSigSort)),
                        Term.mkDomainElement(4, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(4, orderedSigSort)),
                        Term.mkDomainElement(5, orderedSigSort)),
                Term.mkEq(
                        Term.mkApp(nextFunc.name(), Term.mkDomainElement(5, orderedSigSort)),
                        Term.mkDomainElement(6, orderedSigSort))));

        // we have the range axiom after running the scalar caster
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_scope1() {
        // edge case: what happens when the scope is 1?
        // no axioms and [[(x,y) \in next]] := ([[x \in orderedSig]] && x != @_1) && next(x) = y
        when(scoper.sig2scope(orderedSig)).thenReturn(1);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 1));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        // there should be no axioms
        assertEquals(0, context.getTheory().axioms().size());

        // we have the range axiom after running the scalar caster
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_definitions() {
        // next behaves well when using definitions
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
        defnTranslator.translate(ordSig, context);

        Scalar scalar = defnTranslator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

        // there should be no functions or axioms
        assertTrue(context.getTheory().functionDeclarations().isEmpty());
        assertTrue(context.getTheory().axioms().isEmpty());

        // there should be one definition, next
        assertEquals(1, context.getTheory().functionDefinitions().size());
        FunctionDefinition nextDefn = context.getTheory().functionDefinitions().head();
        assertEquals(1, nextDefn.argSorts().size());
        assertEquals(orderedSigSort, nextDefn.argSorts().head());
        assertEquals(orderedSigSort, nextDefn.resultSort());
        Var x = Term.mkVar("x_0");
        Term nextBody = Term.mkIfThenElse(Term.mkEq(x, Term.mkDomainElement(1, orderedSigSort)),
                Term.mkDomainElement(2, orderedSigSort),
                Term.mkDomainElement(3, orderedSigSort));
        assertEquals(nextBody, nextDefn.body());

        // we have the range axiom after running the scalar caster
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_definitions_notStartingAtDE1() {
        // next behaves well when using definitions and the DE range is [3, 6]
        when(scoper.sig2scope(orderedSig)).thenReturn(4);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(3, 6));
        defnTranslator.translate(ordSig, context);

        Scalar scalar = defnTranslator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

        // there should be no functions or axioms
        assertTrue(context.getTheory().functionDeclarations().isEmpty());
        assertTrue(context.getTheory().axioms().isEmpty());

        // there should be one definition, next
        assertEquals(1, context.getTheory().functionDefinitions().size());
        FunctionDefinition nextDefn = context.getTheory().functionDefinitions().head();
        assertEquals(1, nextDefn.argSorts().size());
        assertEquals(orderedSigSort, nextDefn.argSorts().head());
        assertEquals(orderedSigSort, nextDefn.resultSort());
        Var x = Term.mkVar("x_0");
        Term nextBody = Term.mkIfThenElse(Term.mkEq(x, Term.mkDomainElement(3, orderedSigSort)),
                Term.mkDomainElement(4, orderedSigSort),
                Term.mkIfThenElse(Term.mkEq(x, Term.mkDomainElement(4, orderedSigSort)),
                        Term.mkDomainElement(5, orderedSigSort),
                        Term.mkDomainElement(6, orderedSigSort)));
        assertEquals(nextBody, nextDefn.body());

        // we have the range axiom after running the scalar caster
        verify(rangeAssigner, atLeastOnce()).addRangeAxiom(eq(orderedSig), any(), any());
    }

    @Test
    public void testTranslate_orderedSig_next_definitions_scope1() {
        // edge case: what happens when the scope is 1?
        when(scoper.sig2scope(orderedSig)).thenReturn(1);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 1));
        defnTranslator.translate(ordSig, context);

        Scalar scalar = defnTranslator.castToScalar(ordSig.join(nextField), context);
        assertNotNull(scalar);

        // there should be no functions or axioms
        assertTrue(context.getTheory().functionDeclarations().isEmpty());
        assertTrue(context.getTheory().axioms().isEmpty());

        // there should be one definition, next, although it's not actually necessary!
        assertEquals(1, context.getTheory().functionDefinitions().size());
        FunctionDefinition nextDefn = context.getTheory().functionDefinitions().head();
        assertEquals(1, nextDefn.argSorts().size());
        assertEquals(orderedSigSort, nextDefn.argSorts().head());
        assertEquals(orderedSigSort, nextDefn.resultSort());
        Term nextBody = Term.mkDomainElement(1, orderedSigSort);
        assertEquals(nextBody, nextDefn.body());
    }

    @Test
    public void testCastToScalar_first() {
        // test castToScalar(Ord.first) = (@1: Int, Top), first is hardcoded as the first DE in the range
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(firstField), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        assertNotNull(scalar);
        assertTrue(scalar.isNilary());
        assertEquals(Term.mkDomainElement(1, orderedSigSort), scalar.getNilaryScalar());
        assertEquals(orderedSigSort, scalar.getResultSort());
        assertEquals(Term.mkTop(), scalar.getNilaryGuard());
    }

    @Test
    public void testCastToScalar_first_notDE1() {
        // test castToScalar(Ord.first) = (@first: Int, Top), first is hardcoded as the first DE in the range
        when(scoper.sig2scope(orderedSig)).thenReturn(10);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(5, 10));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(firstField), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        assertNotNull(scalar);
        assertTrue(scalar.isNilary());
        assertEquals(Term.mkDomainElement(5, orderedSigSort), scalar.getNilaryScalar());
        assertEquals(orderedSigSort, scalar.getResultSort());
        assertEquals(Term.mkTop(), scalar.getNilaryGuard());
    }

    @Test
    public void testCastToScalar_next() {
        // test castToScalar(Ord.next) = (x |-> next(x), x |-> inOrderedSig(x) && x != @last)
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Scalar scalar = translator.castToScalar(ordSig.join(nextField), context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        AnnotatedVar x = Term.mkVar("x").of(orderedSigSort);
        assertNotNull(scalar);
        assertFalse(scalar.isNilary());
        assertEquals(1, scalar.getArity());
        assertEquals(orderedSigSort, scalar.getArgSorts().get(0));
        assertEquals(orderedSigSort, scalar.getResultSort());
        assertEquals(Term.mkApp(nextFunc.name(), x.variable()), scalar.getScalar(TermTuple.fromVars(x)));
        Term expectedGuard = Term.mkAnd(
                Term.mkApp("inOrderedSig", x.variable()),
                Term.mkNot(Term.mkEq(x.variable(), Term.mkDomainElement(3, orderedSigSort))));
        assertEquals(expectedGuard, scalar.getGuard(TermTuple.fromVars(x)));
    }

    @Test
    public void testCastToScalar_nextWithNoops() {
        // test castToScalar(NOOP(Ord.next)) = (x |-> next(x), x |-> inOrderedSig(x) && x != @last)
        when(scoper.sig2scope(orderedSig)).thenReturn(3);
        when(rangeAssigner.getDomainElementRange(orderedSig)).thenReturn(new Pair<>(1, 3));
        translator.translate(ordSig, context);

        Expr nextUsage = ExprUnary.Op.NOOP.make(null, ExprUnary.Op.NOOP.make(null, ordSig).cast2int())
                .join(nextField.cast2int().cast2sigint()).cast2int();
        Scalar scalar = translator.castToScalar(nextUsage, context);

        // there should be one function, next: orderedSigSort -> orderedSigSort
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl nextFunc = context.getTheory().functionDeclarations().head();
        assertEquals(1, nextFunc.argSorts().size());
        assertEquals(orderedSigSort, nextFunc.argSorts().head());
        assertEquals(orderedSigSort, nextFunc.resultSort());

        AnnotatedVar x = Term.mkVar("x").of(orderedSigSort);
        assertNotNull(scalar);
        assertFalse(scalar.isNilary());
        assertEquals(1, scalar.getArity());
        assertEquals(Term.mkApp(nextFunc.name(), x.variable()), scalar.getScalar(TermTuple.fromVars(x)));
        Term expectedGuard = Term.mkAnd(
                Term.mkApp("inOrderedSig", x.variable()),
                Term.mkNot(Term.mkEq(x.variable(), Term.mkDomainElement(3, orderedSigSort))));
        assertEquals(expectedGuard, scalar.getGuard(TermTuple.fromVars(x)));
    }

    @Test
    public void testNoOrderingBothParentAndChild_translateParentFirst() {
        // test an error is thrown if you try to order both a parent sig and its child subsig, because that would
        // fix a relationship between the orderings in our implementation
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig(null, "Child", new Pos("", 0, 0), parent);
        Sort orderedSigSort = Sort.mkSortConst("OrderedSort");
        Sig.PrimSig ord1 = new Sig.PrimSig("Ord1", Attr.ONE);
        Sort ordSigSort1 = Sort.mkSortConst("OrdSort1");
        Sig.PrimSig ord2 = new Sig.PrimSig("Ord2", Attr.ONE);
        Sort ordSigSort2 = Sort.mkSortConst("OrdSort2");
        Sig.Field firstField1 = ord1.addField("First", parent.setOf());
        Sig.Field nextField1 = ord1.addField("Next", parent.product(parent));
        Sig.Field firstField2 = ord2.addField("First", child.setOf());
        Sig.Field nextField2 = ord2.addField("Next", child.product(child));

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(policy.getSort(parent)).thenReturn(orderedSigSort);
        when(policy.getSort(child)).thenReturn(orderedSigSort);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty()
                .withSort(orderedSigSort)
                .withSort(ordSigSort1)
                .withSort(ordSigSort2));
        when(policy.getSort(ord1)).thenReturn(ordSigSort1);
        when(policy.getSort(ord2)).thenReturn(ordSigSort2);
        when(rangeAssigner.getDomainElementRange(eq(ord1))).thenReturn(new Pair<>(1, 1));
        when(rangeAssigner.getDomainElementRange(eq(ord2))).thenReturn(new Pair<>(1, 1));
        when(rangeAssigner.getDomainElementRange(eq(parent))).thenReturn(new Pair<>(1, 2));
        when(rangeAssigner.getDomainElementRange(eq(child))).thenReturn(new Pair<>(1, 1));
        ord1.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                parent, ord1.join(firstField1), ord1.join(nextField1))));
        ord2.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                child, ord2.join(firstField2), ord2.join(nextField2))));

        context = new TranslationContext(new PortusOptions(), scoper, policy, rangeAssigner);

        when(scoper.sig2scope(parent)).thenReturn(2);
        when(scoper.sig2scope(child)).thenReturn(1);

        translator.translate(ord1, context);
        assertThrows(ErrorNoPortusSupport.class, () -> translator.translate(ord2, context));
    }

    @Test
    public void testNoOrderingBothParentAndChild_translateChildFirst() {
        // same, but call translate on the child first
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig(null, "Child", new Pos("", 0, 0), parent);
        Sort orderedSigSort = Sort.mkSortConst("OrderedSort");
        Sig.PrimSig ord1 = new Sig.PrimSig("Ord1", Attr.ONE);
        Sort ordSigSort1 = Sort.mkSortConst("OrdSort1");
        Sig.PrimSig ord2 = new Sig.PrimSig("Ord2", Attr.ONE);
        Sort ordSigSort2 = Sort.mkSortConst("OrdSort2");
        Sig.Field firstField1 = ord1.addField("First", parent.setOf());
        Sig.Field nextField1 = ord1.addField("Next", parent.product(parent));
        Sig.Field firstField2 = ord2.addField("First", child.setOf());
        Sig.Field nextField2 = ord2.addField("Next", child.product(child));

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(policy.getSort(parent)).thenReturn(orderedSigSort);
        when(policy.getSort(child)).thenReturn(orderedSigSort);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty()
                .withSort(orderedSigSort)
                .withSort(ordSigSort1)
                .withSort(ordSigSort2));
        when(policy.getSort(ord1)).thenReturn(ordSigSort1);
        when(policy.getSort(ord2)).thenReturn(ordSigSort2);
        when(rangeAssigner.getDomainElementRange(eq(ord1))).thenReturn(new Pair<>(1, 1));
        when(rangeAssigner.getDomainElementRange(eq(ord2))).thenReturn(new Pair<>(1, 1));
        when(rangeAssigner.getDomainElementRange(eq(parent))).thenReturn(new Pair<>(1, 2));
        when(rangeAssigner.getDomainElementRange(eq(child))).thenReturn(new Pair<>(1, 1));
        ord1.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                parent, ord1.join(firstField1), ord1.join(nextField1))));
        ord2.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                child, ord2.join(firstField2), ord2.join(nextField2))));

        context = new TranslationContext(new PortusOptions(), scoper, policy, rangeAssigner);

        when(scoper.sig2scope(parent)).thenReturn(2);
        when(scoper.sig2scope(child)).thenReturn(1);

        translator.translate(ord2, context);
        assertThrows(ErrorNoPortusSupport.class, () -> translator.translate(ord1, context));
    }

}
