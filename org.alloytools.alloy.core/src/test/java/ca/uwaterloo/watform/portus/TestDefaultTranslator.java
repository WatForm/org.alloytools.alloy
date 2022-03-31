package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
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
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.containsInAnyOrder;
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
    private void assertIsMembershipPredicate(FuncDecl func, String name) {
        assertThat(func.name(), startsWith(name));
        assertThat(func.arity(), is(1));
        assertThat(func.argSorts().head(), is(context.univSort));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    // Assert that nothing has been added to the context (except the universal sort).
    private void assertContextEmpty() {
        assertThat(context.getTheory(), is(Theory.empty().withSort(context.univSort)));
    }

    @Test
    public void testTranslate_primSig_singleExactScope() {
        // single signature
        Sig.PrimSig sig = new Sig.PrimSig("TestSig");
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // mock out [[y \in sig]] from the exact scope axiom
        Var y = Term.mkVar("y");
        Term inSigFlag = makeFlagConstant("inSig");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y, sig))), any()))
                .thenReturn(inSigFlag);

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // create the expected exact scope axiom
        // "exists x1, x2: univ . forall y: univ . !(x1 = x2) && ([[y \in S]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term exactScopeAxiom = Term.mkExists(Arrays.asList(x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkForall(y.of(context.univSort), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkIff(inSigFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // this should be the only axiom
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(exactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");

        // scope of univ should be same as scope of the one sig
        assertThat(context.getTotalScope(), is(2));
    }

    @Test
    public void testTranslate_primSig_singleNonExactScope() {
        // single signature
        Sig.PrimSig sig = new Sig.PrimSig("TestSig");
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(false);

        // mock out the non-exact scope axiom's [[xi \in sig]]
        Expr inSig = ExprElementOf.make(Term.mkVar("x"), sig);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inSig)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.get(0)));

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // create the expected non-exact scope axiom
        // "forall x0, x1, x2: univ . [[x0 \in S]] && [[x1 \in S]] && [[x2 \in S]] =>
        // x0 = x1 || x0 = x2 || x1 = x2"
        Var x0 = Term.mkVar("x0");
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term nonExactScopeAxiom = Term.mkForall(
                Arrays.asList(x0.of(context.univSort), x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkImp(
                        Term.mkAnd(
                                makeFlagConstant("inFlag_x0"),
                                makeFlagConstant("inFlag_x1"),
                                makeFlagConstant("inFlag_x2")),
                        Term.mkOr(
                                Term.mkEq(x0, x1),
                                Term.mkEq(x0, x2),
                                Term.mkEq(x1, x2))));

        // this should be the only axiom
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(nonExactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");

        // scope of univ should be same as scope of the one sig
        assertThat(context.getTotalScope(), is(2));
    }

    @Test
    public void testTranslate_primSig_oneSubsigWithExactScope() {
        // signature with subsig with exact scope
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = new Sig.PrimSig("Child", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(2);
        when(mockScoper.isExact(parent)).thenReturn(true);
        when(mockScoper.sig2scope(child)).thenReturn(1);
        when(mockScoper.isExact(child)).thenReturn(true);

        // mock out the subset axiom
        Decl x = child.oneOf("x");
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = x.get().in(parent).forAll(x); // all x: child | x in parent
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // mock out the exact scope axiom's [[x \in child]] and [[x \in parent]]
        Term inChildFlag = makeFlagConstant("xInChild");
        Expr inChild = ExprElementOf.make(Term.mkVar("x"), child);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any()))
                .thenReturn(inChildFlag);
        Term inParentFlag = makeFlagConstant("xInParent");
        Expr inParent = ExprElementOf.make(Term.mkVar("x"), parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inParent)), any()))
                .thenReturn(inParentFlag);

        // delegate to the method under test to translate the child sig
        when(mockRoot.translate(eq(child), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // create the expected exact scope axiom for the parent
        // "exists x1, x2: univ . forall y: univ . !(x1 = x2) && ([[y \in Parent]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var y = Term.mkVar("y");
        Term exactScopeAxiom1 = Term.mkExists(Arrays.asList(x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkForall(y.of(context.univSort), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkIff(inParentFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // create the expected exact scope axiom for the child
        // scope 1: "exists x: univ . forall y: univ . [[y \in Child]] <=> y = x
        Term exactScopeAxiom2 = Term.mkExists(x1.of(context.univSort),
                Term.mkForall(y.of(context.univSort), Term.mkIff(
                        inChildFlag, Term.mkEq(y, x1))));

        // should have two axioms: subset and exact scope
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(subsetFlag),
                isAlphaEquivalentTerm(exactScopeAxiom1),
                isAlphaEquivalentTerm(exactScopeAxiom2)));

        // should have two functions, inParent: Parent -> Bool and inChild: Parent -> Bool
        assertThat(context.getTheory().functionDeclarations().size(), is(2));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, "inParent");
        FuncDecl inChildPred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChildPred, "inChild");

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));

        // scope of univ should be same as scope of the top-level sig
        assertThat(context.getTotalScope(), is(2));
    }

    @Test
    public void testTranslate_primSig_abstractTwoSubsigsOneExact() {
        // abstract signature with two subsigs, one exact and one not
        Sig.PrimSig parent = new Sig.PrimSig("Parent", Attr.ABSTRACT);
        Sig.PrimSig child1 = new Sig.PrimSig("Child1", parent);
        Sig.PrimSig child2 = new Sig.PrimSig("Child2", parent);
        when(mockScoper.sig2scope(parent)).thenReturn(2);
        when(mockScoper.isExact(parent)).thenReturn(true);
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

        // mock out the exact and non-exact scope axiom's [[xi \in sig]]
        Expr inChild = ExprElementOf.make(Term.mkVar("x"), child1);
        Expr inParent = ExprElementOf.make(Term.mkVar("x"), parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.get(0)));
        when(mockRoot.translate(argThat(isAlphaEquivalent(inParent)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.get(0)));

        // delegate to the method under test to translate the child sigs
        when(mockRoot.translate(or(eq(child1), eq(child2)), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // create the expected exact scope axiom for the parent
        // "exists x1, x2: univ . forall y: univ . !(x1 = x2) && ([[y \in S]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var y = Term.mkVar("y");
        Term exactScopeAxiom1 = Term.mkExists(Arrays.asList(x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkForall(y.of(context.univSort), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        // use 'x' since it's the variable name they use
                        Term.mkIff(makeFlagConstant("inFlag_x"), Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // create the expected exact scope axiom for the child
        // "exists x1: univ . forall x: univ . [[x \in child1]] <=> x = x1"
        Var x = Term.mkVar("x");
        Term exactScopeAxiom2 = Term.mkExists(x1.of(context.univSort), Term.mkForall(x.of(context.univSort),
                Term.mkIff(makeFlagConstant("inFlag_x"), Term.mkEq(x, x1))));

        // create the expected non-exact scope axiom for the child
        // "forall x0, x1: univ . [[x0 \in child2]] && [[x1 \in child2]] => x0 = x1"
        Var x0 = Term.mkVar("x0");
        Term nonExactScopeAxiom = Term.mkForall(Arrays.asList(x0.of(context.univSort), x1.of(context.univSort)),
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
                isAlphaEquivalentTerm(exactScopeAxiom1), // exact scope axiom, parent
                isAlphaEquivalentTerm(exactScopeAxiom2), // exact scope axiom, child1
                isAlphaEquivalentTerm(nonExactScopeAxiom))); // non-exact scope axiom, child2

        // should have three membership predicates, one per sort
        assertThat(context.getTheory().functionDeclarations().size(), is(3));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, "inParent");
        //noinspection RedundantCast - IntelliJ thinks it's unnecessary but build fails without it
        FuncDecl inChild1Pred = (FuncDecl) context.getTheory().functionDeclarations().tail().head();
        assertIsMembershipPredicate(inChild1Pred, "inChild1");
        FuncDecl inChild2Pred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChild2Pred, "inChild2");

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));

        // scope of univ should be same as scope of the top-level sig
        assertThat(context.getTotalScope(), is(2));
    }

    @Test
    public void testTranslate_inSig() {
        // test [[v \in Sig]] := inSig(v) where inSig is the membership predicate for Sig
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        when(mockScoper.sig2scope(sig)).thenReturn(1);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // just delegate the sub-translations, we don't care about the generated axioms
        delegateToRealTranslator();
        translator.translate(sig, context);

        Var var = Term.mkVar("v");
        Term result = translator.translate(ExprElementOf.make(var, sig), context);

        // get the membership predicate, should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSig");

        // result must be inSig(v)
        assertEquals(Term.mkApp(inSigPred.name(), var), result);
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
    public void testTranslate_join_arity1x2() {
        // test [[x \in e1 . e2]] := exists y: univ . [[y \in e1]] && [[(y, x) \in e2]]
        // where arity(e1) = 1, arity(e2) = 2
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig).product(Type.make(sig)));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[y \in e1]] and [[(y, x) \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y, e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(y, x)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(x, e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(context.univSort), Term.mkAnd(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_join_arity2x1() {
        // test [[x \in e1 . e2]] := exists y: univ . [[y \in e1]] && [[(y, x) \in e2]]
        // where arity(e1) = 2, arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig).product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x, y) \in e1]] and [[y \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x, y)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y, e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(x, e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(context.univSort), Term.mkAnd(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_join_arity2x2() {
        // test [[(x1, x2) \in e1 . e2]] := exists y: univ . [[(x1, y) \in e1]] && [[(y, x2) \in e2]]
        // where arity(e1) = 2, arity(e2) = 2
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig).product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig).product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), y = Term.mkVar("y");

        // mock out [[(x1, y) \in e1]] and [[(y, x2) \in e2]]
        // they're alpha-equivalent, so just return one after the other
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, y)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(context.univSort), Term.mkAnd(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_join_arity1x3() {
        // test [[(x1, x2) \in e1 . e2]] := exists y: univ . [[y \in e1]] && [[(y, x1, x2) \in e2]]
        // where arity(e1) = 1, arity(e2) = 3
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig)
                .product(Type.make(sig)).product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), y = Term.mkVar("y");

        // mock out [[y \in e1]] and [[(y, x1, x2) \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y, e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(y, x1, x2)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(context.univSort), Term.mkAnd(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_crossProduct_arity1x1() {
        // test [[(x1, x2) \in e1->e2]] := [[x1 \in e1]] && [[x2 \in e2]]
        // where arity(e1) = 1, arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");

        // mock out [[x1 \in e1]] and [[x2 \in e2]]
        // they're alpha-equivalent, so just return one after the other
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1, e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1.product(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_crossProduct_arity1x2() {
        // test [[(x1, x2, x3) \in e1->e2]] := [[x1 \in e1]] && [[(x2, x3) \in e2]]
        // where arity(e1) = 1, arity(e2) = 2
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig).product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), x3 = Term.mkVar("x3");

        // mock out [[x1 \in e1]] and [[(x2, x3) \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1, e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x2, x3)), e1))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e1.product(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_crossProduct_arity2x1() {
        // test [[(x1, x2, x3) \in e1->e2]] := [[(x1, x2) \in e1]] && [[x3 \in e2]]
        // where arity(e1) = 2, arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig).product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), x3 = Term.mkVar("x3");

        // mock out [[(x1, x2) \in e1]] and [[x3 \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x3, e1))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e1.product(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_domainRestriction_arity1() {
        // test [[x \in e1 <: e2]] := [[x \in e1]] && [[x \in e2]] where arity(e1) = arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x = Term.mkVar("x");

        // mock out [[x \in e1]] and [[x \in e2]]
        // they're alpha-equivalent, so just return one flag after the other
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(ExprElementOf.make(x, e1.domain(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_domainRestriction_arity3() {
        // test [[(x1,x2,x3) \in e1 <: e2]] := [[x \in e1]] && [[(x1,x2,x3) \in e2]]
        // where arity(e1) = 1, arity(e2) = 3
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig)
                .product(Type.make(sig)).product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), x3 = Term.mkVar("x3");

        // mock out [[x \in e1]] and [[(x1,x2,x3) \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1, e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(
                ConstList.make(Arrays.asList(x1, x2, x3)), e1.domain(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }


    @Test
    public void testTranslate_rangeRestriction_arity1() {
        // test [[x \in e1 :> e2]] := [[x \in e1]] && [[x \in e2]] where arity(e1) = arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x = Term.mkVar("x");

        // mock out [[x \in e1]] and [[x \in e2]]
        // they're alpha-equivalent, so just return one flag after the other
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(ExprElementOf.make(x, e1.range(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_rangeRestriction_arity3() {
        // test [[(x1,x2,x3) \in e1 :> e2]] := [[(x1,x2,x3) \in e1]] && [[x \in e2]]
        // where arity(e1) = 3, arity(e2) = 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig)
                .product(Type.make(sig)).product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), x3 = Term.mkVar("x3");

        // mock out [[(x1,x2,x3) \in e2]] and [[x \in e1]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1, e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(
                ConstList.make(Arrays.asList(x1, x2, x3)), e1.range(e2)), context);
        Term expected = Term.mkAnd(flagInE1, flagInE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_override_arity1() {
        // Override special case: test [[x \in e1 ++ e2]] := [[x \in e1 + e2]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var x = Term.mkVar("x");

        // mock out [[x \in e1 + e2]]
        Var flagUnion = makeFlagConstant("inUnion");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, e1.plus(e2)))), any()))
                .thenReturn(flagUnion);

        Term result = translator.translate(ExprElementOf.make(x, e1.override(e2)), context);
        assertThat(result, is(flagUnion));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_override_arity2() {
        // test [[(x1, x2) \in e1 ++ e2]] := [[(x1, x2) \in e2]]
        // || ([[(x1, x2) \in e1]] && !exists y. [[(x1, y) \in e2]])
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig).product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig).product(Type.make(sig)));
        // note: use y0 to match the generated variable name for more robust testing
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), y = Term.mkVar("y0");

        // mock out all the element-of checks
        Var flagBothInE1 = makeFlagConstant("bothInE1");
        Var flagBothInE2 = makeFlagConstant("bothInE2");
        Var flagX1InE2 = makeFlagConstant("x1InE2");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1))), any()))
                .thenReturn(flagBothInE1);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e2))), any()))
                .thenReturn(flagBothInE2);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, y)), e2))), any()))
                .thenReturn(flagX1InE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1.override(e2)), context);
        Term expected = Term.mkOr(flagBothInE2, Term.mkAnd(
                flagBothInE1, Term.mkNot(Term.mkExists(y.of(context.univSort), flagX1InE2))));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_override_arity3() {
        // test [[(x1, x2, x3) \in e1 ++ e2]] := [[(x1, x2, x3) \in e2]]
        // || ([[(x1, x2, x3) \in e1]] && !exists y1, y2. [[(x1, y1, y2) \in e2]])
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig).product(Type.make(sig))
                .product(Type.make(sig)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig).product(Type.make(sig))
                .product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2"), x3 = Term.mkVar("x3");
        // match the generated variable names
        Var y1 = Term.mkVar("y0"), y2 = Term.mkVar("y1");

        // mock out all the element-of checks
        Var flagAllInE1 = makeFlagConstant("allInE1");
        Var flagAllInE2 = makeFlagConstant("allInE2");
        Var flagX1InE2 = makeFlagConstant("x1InE2");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e1))), any()))
                .thenReturn(flagAllInE1);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e2))), any()))
                .thenReturn(flagAllInE2);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, y1, y2)), e2))), any()))
                .thenReturn(flagX1InE2);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2, x3)), e1.override(e2)), context);
        Term expected = Term.mkOr(flagAllInE2, Term.mkAnd(
                flagAllInE1, Term.mkNot(Term.mkExists(
                        Arrays.asList(y1.of(context.univSort), y2.of(context.univSort)), flagX1InE2))));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_in_arity1() {
        // test [[e1 \in e2]] := forall x: univ . [[x \in e1]] => [[x \in e2]] for arity 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.in(e2), context);
        Term expected = Term.mkForall(x.of(context.univSort), Term.mkImp(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_in_arity2() {
        // test [[e1 \in e2]] := forall x1, x2: univ . [[(x1,x2) \in e1]] => [[(x1,x2) \in e2]]
        Sig.PrimSig sig1 = new Sig.PrimSig("S1");
        Sig.PrimSig sig2 = new Sig.PrimSig("S2");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig1).product(Type.make(sig2)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig1).product(Type.make(sig2)));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");

        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.in(e2), context);
        Term expected = Term.mkForall(Arrays.asList(x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkImp(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_eq_arity1() {
        // test [[e1 = e2]] := forall x: univ . [[x \in e1]] <=> [[x \in e2]] for arity 1
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.equal(e2), context);
        Term expected = Term.mkForall(x.of(context.univSort), Term.mkIff(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_eq_arity2() {
        // test [[e1 = e2]] := forall x1, x2: univ . [[(x1,x2) \in e1]] <=> [[(x1,x2) \in e2]]
        Sig.PrimSig sig1 = new Sig.PrimSig("S1");
        Sig.PrimSig sig2 = new Sig.PrimSig("S2");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig1).product(Type.make(sig2)));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig1).product(Type.make(sig2)));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");

        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.equal(e2), context);
        Term expected = Term.mkForall(Arrays.asList(x1.of(context.univSort), x2.of(context.univSort)),
                Term.mkIff(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_notIn() {
        // test [[e1 !in e2]] := [[not (e1 in e2)]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isSameAs(e1.in(e2).not())), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprBinary.Op.NOT_IN.make(null, null, e1, e2), context);
        assertEquals(flag, result);
    }

    @Test
    public void testTranslate_notEq() {
        // test [[e1 != e2]] := [[not (e1 = e2)]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isSameAs(e1.equal(e2).not())), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprBinary.Op.NOT_EQUALS.make(null, null, e1, e2), context);
        assertEquals(flag, result);
    }

    @Test
    public void testTranslate_transpose() {
        // test [[(x1, x2) \in ~e]] := [[(x2, x1) \in e]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");

        Var flagSwapped = makeFlagConstant("swapped");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(ConstList.make(Arrays.asList(x2, x1)), e))), any()))
                .thenReturn(flagSwapped);

        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), e.transpose()), context);
        assertEquals(flagSwapped, result);
    }

    @Test
    public void testTranslate_all_oneVar() {
        // test [[all x: e | f]] := forall x: univ . [[x \in e]] => [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestVariable("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // "e" gets translated to "one e" at some point
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e))), any()))
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
        Term expected = Term.mkForall(fortressX.get().of(context.univSort), Term.mkImp(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasVarMapping("x"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_all_twoVars() {
        // test [[all x1: e1, x2: e2 | f]] := forall x1, x2: univ . [[x1 \in e1]] && [[x2 \in e2]] => [[f]]
        Sig.PrimSig sig1 = new Sig.PrimSig("S1"), sig2 = new Sig.PrimSig("S2");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig1));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig2));
        Decl x1 = e1.oneOf("x1"), x2 = e2.oneOf("x2");
        ExprVar f = makeTestVariable("f");
        Var flagInE1 = makeFlagConstant("x1InE1"), flagInE2 = makeFlagConstant("x2InE2");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e1))), any()))
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
                Arrays.asList(fortressX1.get().of(context.univSort), fortressX2.get().of(context.univSort)),
                Term.mkImp(Term.mkAnd(flagInE1, flagInE2), flagSub));
        assertEquals(expected, result);

        // make sure the mappings were removed after translation
        assertFalse(context.hasVarMapping("x1"));
        assertFalse(context.hasVarMapping("x2"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_some() {
        // test [[some x: e | f]] := exists x: univ . [[x \in e]] && [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestVariable("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // "e" gets translated to "one e" at some point
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX, e))), any()))
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
        Term expected = Term.mkExists(fortressX.get().of(context.univSort), Term.mkAnd(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasVarMapping("x"));
        assertContextEmpty();
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
        assertContextEmpty();
    }

    @Test
    public void testTranslate_lone() {
        // test [[lone x: e | f]] := forall x, y: univ . [[x \in e]] && [[y \in e]] && [[f]] && [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", context.univSort, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", context.univSort, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e))), any())).then(ctx -> {
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
        Term expected = Term.mkForall(Arrays.asList(x.of(context.univSort), y.of(context.univSort)), Term.mkImp(
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
        // test [[one x: e | f]] := exists x: univ . [[x \in e]] && [[f]] && forall y: S . [[y \in e]] &&
        //   [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", context.univSort, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", context.univSort, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e))), any())).then(ctx -> {
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
        Term expected = Term.mkExists(x.of(context.univSort), Term.mkAnd(
                Term.mkApp("inE", x),
                Term.mkApp("f", x),
                Term.mkForall(y.of(context.univSort), Term.mkImp(
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
        assertContextEmpty();
    }

    @Test
    public void testTranslate_univ() {
        // test [[x \in univ]] := true
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x, Sig.UNIV), context);
        assertEquals(Term.mkTop(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_iden() {
        // test [[(x1, x2) \in iden] := x1 = x2
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");
        Term result = translator.translate(
                ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), ExprConstant.IDEN), context);
        assertEquals(Term.mkEq(x1, x2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_emptyness() {
        // test [[x \in none] := false
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x, ExprConstant.EMPTYNESS), context);
        assertEquals(Term.mkBottom(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_noop() {
        // test [[NOOP(e)]] := [[e]], because Alloy has no-ops in its AST
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        Term result = translator.translate(ExprUnary.Op.NOOP.make(null, e), context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_nestedNoop() {
        // test [[NOOP(NOOP(e))]] := [[e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        Term result = translator.translate(
                ExprUnary.Op.NOOP.make(null, ExprUnary.Op.NOOP.make(null, e)), context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inNoop() {
        // test [[x \in NOOP(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x, ExprUnary.Op.NOOP.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inNestedNoop() {
        // test [[x \in NOOP(NOOP(e))]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x, ExprUnary.Op.NOOP.make(null,
                ExprUnary.Op.NOOP.make(null, e)));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

}
