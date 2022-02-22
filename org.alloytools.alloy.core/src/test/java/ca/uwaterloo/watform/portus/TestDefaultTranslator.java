package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
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

import static ca.uwaterloo.watform.portus.AlloyASTMatcher.isAlphaEquivalent;
import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.hamcrest.Matchers.hasSize;
import static org.hamcrest.Matchers.is;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.Matchers.startsWith;
import static org.junit.Assert.assertEquals;
import static org.mockito.AdditionalMatchers.or;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
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

    // Fortress flag constants are used as mock return values of translations.
    private Var makeFlagConstant(String label) {
        return Term.mkVar(label);
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

}
