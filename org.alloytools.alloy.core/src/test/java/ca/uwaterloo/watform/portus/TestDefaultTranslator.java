package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
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
import java.util.concurrent.atomic.AtomicReference;

import static ca.uwaterloo.watform.portus.AlloyASTMatcher.isAlphaEquivalent;
import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.hamcrest.Matchers.hasSize;
import static org.hamcrest.Matchers.is;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.Matchers.startsWith;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.AdditionalMatchers.or;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class TestDefaultTranslator {

    private Translator mockRoot;
    private Translator translator;

    private ScopeComputer mockScoper;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        translator = new DefaultTranslator(mockRoot);
        mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(A4Reporter.NOP, mockScoper);
    }

    // Alloy test variables are used as placeholders in Alloy test expressions.
    private ExprVar makeTestVariable(String label) {
        return ExprVar.make(null, label);
    }

    private ExprVar makeTestVarWithType(String label, Type type) {
        return ExprVar.make(null, label, type);
    }

    // Fortress flag constants are used as mock return values of translations.
    private Var makeFlagConstant(String label) {
        return Term.mkVar(label);
    }

    // Delegate to the real translator for any translation.
    // This should go before other when() calls so it can be overriden for specific arguments.
    // Also, you must use doReturn(...).when(...) for overrides: https://stackoverflow.com/a/34172381.
    private void delegateToRealTranslator() {
        when(mockRoot.translate(any(), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));
    }

    // Assert that a function declaration is a membership predicate for the given sort.
    private void assertIsMembershipPredicate(FuncDecl func, Sort sort, String name) {
        assertThat(func.name(), startsWith(name));
        assertThat(func.arity(), is(1));
        assertThat(func.argSorts().head(), is(sort));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    // Assert that nothing has been added to the context.
    private void assertContextEmpty() {
        assertThat(context.getTheory(), is(Theory.empty()));
    }

    @Test
    public void testTranslate_primSig_single() {
        // single signature
        Sig.PrimSig sig = new Sig.PrimSig("TestSig");
        when(mockScoper.sig2scope(sig)).thenReturn(5);

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // shouldn't have any axioms to translate
        verify(mockRoot, never()).translate(any(), any());

        // should have just one sort which bears its name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort sort = context.getSigSort(sig);
        assertThat(sort, is(notNullValue()));
        assertThat(sort.name(), startsWith("TestSig"));
        assertThat(context.getSortScope(sort), is(5));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, sort, "inTestSig");
    }

    @Test
    public void testTranslate_primSig_oneSubsigWithExactScope() {
        // signature with subsig with exact scope
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig("Child", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(3);
        when(mockScoper.sig2scope(child)).thenReturn(2);
        when(mockScoper.isExact(child)).thenReturn(true);

        // mock out the subset axiom
        Decl x = child.oneOf("x");
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = x.get().in(parent).forAll(x); // all x: child | x in parent
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // mock out the exact scope axiom's [[x \in child]]
        Term inChildFlag = makeFlagConstant("xInChild");
        Expr inChild = ExprElementOf.make(Term.mkVar("x"), child);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any()))
                .thenReturn(inChildFlag);

        // delegate to the method under test to translate the child sig
        when(mockRoot.translate(eq(child), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // should have just one sort with same name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort parentSort = context.getSigSort(parent);
        assertThat(parentSort, is(notNullValue()));
        assertThat(parentSort.name(), startsWith("Parent"));
        assertThat(context.getSortScope(parentSort), is(3));

        // create the expected exact scope axiom
        // "exists x1, x2: parent . forall y: parent. !(x1 = x2) && ([[y \in sort]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var y = Term.mkVar("y");
        Term exactScopeAxiom = Term.mkExists(Arrays.asList(x1.of(parentSort), x2.of(parentSort)),
                Term.mkForall(y.of(parentSort), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkIff(inChildFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // should have two axioms: subset and exact scope
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(subsetFlag),
                isAlphaEquivalentTerm(exactScopeAxiom)));

        // should have two functions, inParent: Parent -> Bool and inChild: Parent -> Bool
        assertThat(context.getTheory().functionDeclarations().size(), is(2));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, parentSort, "inParent");
        FuncDecl inChildPred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChildPred, parentSort, "inChild");

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_primSig_oneSubsigNonExactScope() {
        // signature with subsig with non-exact scope
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig("Child", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(3);
        when(mockScoper.sig2scope(child)).thenReturn(2);
        when(mockScoper.isExact(child)).thenReturn(false);

        // mock out the subset axiom
        Decl x = child.oneOf("x");
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = x.get().in(parent).forAll(x); // all x: child | x in parent
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // mock out the non-exact scope axiom's [[xi \in child]]
        Expr inChild = ExprElementOf.make(Term.mkVar("x"), child);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.get(0)));

        // delegate to the method under test to translate the child sig
        when(mockRoot.translate(eq(child), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // should have just one sort with same name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort parentSort = context.getSigSort(parent);
        assertThat(parentSort, is(notNullValue()));
        assertThat(parentSort.name(), startsWith("Parent"));
        assertThat(context.getSortScope(parentSort), is(3));

        // create the expected non-exact scope axiom
        // "forall x0, x1, x2: parent . [[x0 \in child]] && [[x1 \in child]] && [[x2 \in child]] =>
        // x0 = x1 || x0 = x2 || x1 = x2"
        Var x0 = Term.mkVar("x0");
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term nonExactScopeAxiom = Term.mkForall(
                Arrays.asList(x0.of(parentSort), x1.of(parentSort), x2.of(parentSort)),
                Term.mkImp(
                        Term.mkAnd(
                                makeFlagConstant("inFlag_x0"),
                                makeFlagConstant("inFlag_x1"),
                                makeFlagConstant("inFlag_x2")),
                        Term.mkOr(
                                Term.mkEq(x0, x1),
                                Term.mkEq(x0, x2),
                                Term.mkEq(x1, x2))));

        // should have two axioms: subset and non-exact scope
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(subsetFlag),
                isAlphaEquivalentTerm(nonExactScopeAxiom)));

        // should have two functions, inParent: Parent -> Bool and inChild: Parent -> Bool
        assertThat(context.getTheory().functionDeclarations().size(), is(2));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, parentSort, "inParent");
        FuncDecl inChildPred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChildPred, parentSort, "inChild");

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_primSig_abstractTwoSubsigsOneExact() {
        // abstract signature with two subsigs, one exact and one not
        Sig.PrimSig parent = new Sig.PrimSig("Parent", Attr.ABSTRACT);
        Sig.PrimSig child1 = new Sig.PrimSig("Child1", parent);
        Sig.PrimSig child2 = new Sig.PrimSig("Child2", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(2);
        when(mockScoper.sig2scope(child1)).thenReturn(1);
        when(mockScoper.sig2scope(child2)).thenReturn(1);
        when(mockScoper.isExact(child1)).thenReturn(true);
        when(mockScoper.isExact(child2)).thenReturn(false);

        // mock out the subset axiom for both
        // need to do it like this because the naive way fails due to alpha-equivalence
        Decl xChild = child1.oneOf("x1"); // doesn't matter which due to alpha-equivalence
        Expr subsetAxiom = xChild.get().in(parent).forAll(xChild); // all x: child1 | x in parent
        // this generates flag constants like "subset_one_Child1"
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any())).then(
                ctx -> {
                    ExprQt expr = ctx.getArgument(0);
                    Expr bindExpr = expr.decls.get(0).expr;
                    return makeFlagConstant("subset_" + bindExpr.toString().replace(' ', '_'));
                });

        // mock out the abstract/cover axiom
        Decl xParent = parent.oneOf("x");
        // all x: parent | x in child1 or x in child2
        Expr coverAxiom = xParent.get().in(child1).or(xParent.get().in(child2)).forAll(xParent);
        Term coverFlag = makeFlagConstant("cover");
        when(mockRoot.translate(argThat(isAlphaEquivalent(coverAxiom)), any()))
                .thenReturn(coverFlag);

        // mock out the disjointness axiom
        // all x1: child1, x2: child2 | not (x1 = x2)
        Decl xChild1 = child1.oneOf("x1");
        Decl xChild2 = child2.oneOf("x2");
        Expr disjointAxiom = xChild1.get().equal(xChild2.get()).not().forAll(xChild1, xChild2);
        Term disjointFlag = makeFlagConstant("disjoint");
        when(mockRoot.translate(argThat(isAlphaEquivalent(disjointAxiom)), any()))
                .thenReturn(disjointFlag);

        // mock out the exact and non-exact scope axiom's [[xi \in childN]]
        Expr inChild = ExprElementOf.make(Term.mkVar("x"), child1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.get(0)));

        // delegate to the method under test to translate the child sigs
        when(mockRoot.translate(or(eq(child1), eq(child2)), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // should have just one sort with same name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort parentSort = context.getSigSort(parent);
        assertThat(parentSort, is(notNullValue()));
        assertThat(parentSort.name(), startsWith("Parent"));
        assertThat(context.getSortScope(parentSort), is(2));

        // create the expected exact scope axiom
        // "exists x1: parent . forall x: parent . [[x \in child1]] <=> x = x1"
        Var x1 = Term.mkVar("x1");
        Var x = Term.mkVar("x");
        Term exactScopeAxiom = Term.mkExists(x1.of(parentSort), Term.mkForall(x.of(parentSort),
                Term.mkIff(makeFlagConstant("inFlag_x"), Term.mkEq(x, x1))));

        // create the expected non-exact scope axiom
        // "forall x0, x1: parent . [[x0 \in child2]] && [[x1 \in child2]] => x0 = x1"
        Var x0 = Term.mkVar("x0");
        Term nonExactScopeAxiom = Term.mkForall(Arrays.asList(x0.of(parentSort), x1.of(parentSort)),
                Term.mkImp(
                        Term.mkAnd(
                                makeFlagConstant("inFlag_x0"),
                                makeFlagConstant("inFlag_x1")),
                        Term.mkEq(x0, x1)));

        // should have exactly these axioms
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(makeFlagConstant("subset_one_Child1")), // subset axiom, child1
                is(makeFlagConstant("subset_one_Child2")), // subset axiom, child2
                is(disjointFlag), // disjoint axiom
                is(coverFlag), // cover/abstract axiom
                isAlphaEquivalentTerm(exactScopeAxiom), // exact scope axiom, child1
                isAlphaEquivalentTerm(nonExactScopeAxiom))); // non-exact scope axiom, child2

        // should have three membership predicates, one per sort
        assertThat(context.getTheory().functionDeclarations().size(), is(3));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, parentSort, "inParent");
        //noinspection RedundantCast - IntelliJ thinks it's unnecessary but build fails without it
        FuncDecl inChild1Pred = (FuncDecl) context.getTheory().functionDeclarations().tail().head();
        assertIsMembershipPredicate(inChild1Pred, parentSort, "inChild1");
        FuncDecl inChild2Pred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChild2Pred, parentSort, "inChild2");

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_and_twoConjuncts() {
        // test [[x1 and x2]] := [[x1]] && [[x2]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        Term result = translator.translate(x1.and(x2), context);
        assertEquals(Term.mkAnd(flagX1, flagX2), result);
        assertContextEmpty(); // shouldn't change context
    }

    @Test
    public void testTranslate_and_threeConjuncts() {
        // test [[x1 and x2 and x3]] := [[x1]] && [[x2]] && [[x3]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2"),
                x3 = makeTestVariable("x3");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2"),
                flagX3 = makeFlagConstant("x3");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        when(mockRoot.translate(eq(x3), any())).thenReturn(flagX3);
        Term result = translator.translate(x1.and(x2).and(x3), context);
        assertEquals(Term.mkAnd(flagX1, flagX2, flagX3), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_or_twoDisjuncts() {
        // test [[x1 or x2]] := [[x1]] || [[x2]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        Term result = translator.translate(x1.or(x2), context);
        assertEquals(Term.mkOr(flagX1, flagX2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_or_threeDisjuncts() {
        // test [[x1 or x2 or x3]] := [[x1]] || [[x2]] || [[x3]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2"),
                x3 = makeTestVariable("x3");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2"),
                flagX3 = makeFlagConstant("x3");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        when(mockRoot.translate(eq(x3), any())).thenReturn(flagX3);
        Term result = translator.translate(x1.or(x2).or(x3), context);
        assertEquals(Term.mkOr(flagX1, flagX2, flagX3), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_implies() {
        // test [[x1 implies x2]] := [[x1]] => [[x2]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        Term result = translator.translate(x1.implies(x2), context);
        assertEquals(Term.mkImp(flagX1, flagX2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_iff() {
        // test [[x1 iff x2]] := [[x1]] <=> [[x2]]
        ExprVar x1 = makeTestVariable("x1"), x2 = makeTestVariable("x2");
        Var flagX1 = makeFlagConstant("x1"), flagX2 = makeFlagConstant("x2");
        when(mockRoot.translate(eq(x1), any())).thenReturn(flagX1);
        when(mockRoot.translate(eq(x2), any())).thenReturn(flagX2);
        Term result = translator.translate(x1.iff(x2), context);
        assertEquals(Term.mkIff(flagX1, flagX2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_not() {
        // test [[not x]] := ![[x]]
        ExprVar x = makeTestVariable("x");
        Var flagX = makeFlagConstant("x");
        when(mockRoot.translate(eq(x), any())).thenReturn(flagX);
        Term result = translator.translate(x.not(), context);
        assertEquals(Term.mkNot(flagX), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_union_twoSets() {
        // test [[x \in e1 + e2]] := [[x \in e1]] || [[x \in e2]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2");
        Var x = makeFlagConstant("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x, e1.plus(e2)), context);
        assertEquals(Term.mkOr(flag1, flag2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_union_threeSets() {
        // test [[x \in e1 + e2 + e3]] := [[x \in e1]] || [[x \in e2]] || [[x \in e3]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2"),
                e3 = makeTestVariable("e3");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2"),
                flag3 = makeFlagConstant("xInE3");
        Var x = makeFlagConstant("x");

        // delegate back to the mocked object for others
        delegateToRealTranslator();
        doReturn(flag1).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e1))), any());
        doReturn(flag2).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e2))), any());
        doReturn(flag3).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e3))), any());

        Term result = translator.translate(ExprElementOf.make(x, e1.plus(e2).plus(e3)), context);

        // we translate into nested OrLists, oh well...
        assertEquals(Term.mkOr(Term.mkOr(flag1, flag2), flag3), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_intersect_twoSets() {
        // test [[x \in e1 & e2]] := [[x \in e1]] && [[x \in e2]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2");
        Var x = makeFlagConstant("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x, e1.intersect(e2)), context);
        assertEquals(Term.mkAnd(flag1, flag2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_intersect_threeSets() {
        // test [[x \in e1 & e2 & e3]] := [[x \in e1]] && [[x \in e2]] && [[x \in e3]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2"),
                e3 = makeTestVariable("e3");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2"),
                flag3 = makeFlagConstant("xInE3");
        Var x = makeFlagConstant("x");

        // delegate back to the mocked object for others
        delegateToRealTranslator();
        doReturn(flag1).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e1))), any());
        doReturn(flag2).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e2))), any());
        doReturn(flag3).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x, e3))), any());

        Term result = translator.translate(ExprElementOf.make(x, e1.intersect(e2).intersect(e3)), context);

        // we translate into nested AndLists, oh well...
        assertEquals(Term.mkAnd(Term.mkAnd(flag1, flag2), flag3), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_setDifference() {
        // test [[x \in e1 - e2]] := [[x \in e1]] && ![[x \in e2]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2");
        Var x = makeFlagConstant("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x, e1.minus(e2)), context);
        assertEquals(Term.mkAnd(flag1, Term.mkNot(flag2)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_all_oneVar() {
        // test [[all x: e | f]] := forall x: S . [[x \in e]] => [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestVariable("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // set up a sort ahead of time so we don't have to translate that
        Sort sort = Sort.mkSortConst("S");
        context.addSort(sort, 3);
        context.setSigSort(sig, sort);

        // "e" gets translated to "one e" at some point
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e.oneOf()))), any()))
                .thenReturn(flagInE);

        AtomicReference<Var> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            fortressX.set(context.getVarMapping("x"));
            return flagSub;
        });

        Term result = translator.translate(f.forAll(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(fortressX.get().of(sort), Term.mkImp(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_all_twoVars() {
        // test [[all x1: e1, x2: e2 | f]] := forall x1: S1, x2: S2 . [[x1 \in e1]] && [[x2 \in e2]] => [[f]]
        Sig.PrimSig sig1 = new Sig.PrimSig("S1"), sig2 = new Sig.PrimSig("S2");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig1));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig2));
        Decl x1 = e1.oneOf("x1"), x2 = e2.oneOf("x2");
        ExprVar f = makeTestVariable("f");
        Var flagInE1 = makeFlagConstant("x1InE1"), flagInE2 = makeFlagConstant("x2InE2");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // set up sorts
        Sort sort1 = Sort.mkSortConst("S1"), sort2 = Sort.mkSortConst("S2");
        context.addSort(sort1, 3);
        context.setSigSort(sig1, sort1);
        context.addSort(sort2, 3);
        context.setSigSort(sig2, sort2);

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e1.oneOf()))), any()))
                .thenReturn(flagInE1, flagInE2);

        AtomicReference<Var> fortressX1 = new AtomicReference<>();
        AtomicReference<Var> fortressX2 = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure x1 and x2 have mappings here and capture them
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x1"));
            assertTrue(context.hasVarMapping("x2"));
            fortressX1.set(context.getVarMapping("x1"));
            fortressX2.set(context.getVarMapping("x2"));
            return flagSub;
        });

        Term result = translator.translate(f.forAll(x1, x2), context);
        assertNotNull(fortressX1.get()); // make sure we captured references, so we translated [[f]]
        assertNotNull(fortressX2.get());
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(
                Arrays.asList(fortressX1.get().of(sort1), fortressX2.get().of(sort2)),
                Term.mkImp(Term.mkAnd(flagInE1, flagInE2), flagSub));
        assertEquals(expected, result);

        // make sure the mappings were removed after translation
        assertFalse(context.hasVarMapping("x1"));
        assertFalse(context.hasVarMapping("x2"));
    }

    @Test
    public void testTranslate_some() {
        // test [[some x: e | f]] := exists x: S . [[x \in e]] && [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestVariable("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // set up a sort ahead of time so we don't have to translate that
        Sort sort = Sort.mkSortConst("S");
        context.addSort(sort, 3);
        context.setSigSort(sig, sort);

        // "e" gets translated to "one e" at some point
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e.oneOf()))), any()))
                .thenReturn(flagInE);

        AtomicReference<Var> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            fortressX.set(context.getVarMapping("x"));
            return flagSub;
        });

        Term result = translator.translate(f.forSome(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkExists(fortressX.get().of(sort), Term.mkAnd(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_no() {
        // test [[no x: e | f]] := [[all x: e | not f]]
        ExprVar e = makeTestVariable("e");
        Decl x = e.oneOf("x");
        ExprVar f = makeTestVariable("f");
        Var expectedFlag = makeFlagConstant("expected");

        // ExprQt doesn't override isSame unfortunately, so we have to use isAlphaEquivalent
        Expr expected = f.not().forAll(x);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expected)), any()))
                .thenReturn(expectedFlag);

        assertEquals(expectedFlag, translator.translate(f.forNo(x), context));
    }

    @Test
    public void testTranslate_lone() {
        // test [[lone x: e | f]] := forall x, y: S . [[x \in e]] && [[y \in e]] && [[f]] && [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // set up the sort in the theory so we don't have to generate it
        Sort sort = Sort.mkSortConst("S");
        context.addSort(sort, 3);
        context.setSigSort(sig, sort);

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", sort, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", sort, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e.oneOf()))), any())).then(ctx -> {
            // make sure the variable appears in the context
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            return Term.mkApp("inE", context.getVarMapping("x")); // will be substituted with y
        });

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure the variable (still) appears in the context
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            return Term.mkApp("f", context.getVarMapping("x")); // will be substituted with y
        });

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term expected = Term.mkForall(Arrays.asList(x.of(sort), y.of(sort)), Term.mkImp(
                Term.mkAnd(
                        Term.mkApp("inE", x),
                        Term.mkApp("inE", y),
                        Term.mkApp("f", x),
                        Term.mkApp("f", y)),
                Term.mkEq(x, y)));

        Term result = translator.translate(f.forLone(alloyX), context);
        assertThat(result, isAlphaEquivalentTerm(expected));

        // make sure the x |-> fortressX mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_one() {
        // test [[one x: e | f]] := exists x: S . [[x \in e]] && [[f]] && forall y: S . [[y \in e]] &&
        //   [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // set up the sort in the theory so we don't have to generate it
        Sort sort = Sort.mkSortConst("S");
        context.addSort(sort, 3);
        context.setSigSort(sig, sort);

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", sort, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", sort, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e.oneOf()))), any())).then(ctx -> {
            // make sure the variable appears in the context
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            return Term.mkApp("inE", context.getVarMapping("x")); // will be substituted with y
        });

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure the variable (still) appears in the context
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            return Term.mkApp("f", context.getVarMapping("x")); // will be substituted with y
        });

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term expected = Term.mkExists(x.of(sort), Term.mkAnd(
                Term.mkApp("inE", x),
                Term.mkApp("f", x),
                Term.mkForall(y.of(sort), Term.mkImp(
                        Term.mkAnd(
                                Term.mkApp("inE", y),
                                Term.mkApp("f", y)),
                        Term.mkEq(x, y)))));

        Term result = translator.translate(f.forOne(alloyX), context);
        assertThat(result, isAlphaEquivalentTerm(expected));

        // make sure the x |-> fortressX mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_variable() {
        // test [[x \in v]] := x = v for an Alloy variable v
        // explicitly set the variable mapping in the context
        ExprVar alloyVar = makeTestVariable("v");
        Var x = Term.mkVar("x");
        Var v = Term.mkVar("v");
        context.addVarMapping(alloyVar.label, v);

        Term result = translator.translate(ExprElementOf.make(x, alloyVar), context);
        assertEquals(Term.mkEq(x, v), result);
    }

}
