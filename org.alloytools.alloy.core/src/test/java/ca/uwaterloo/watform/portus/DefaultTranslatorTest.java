package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.DomainElement;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BiFunction;

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
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;
import static org.mockito.AdditionalMatchers.or;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class DefaultTranslatorTest {

    private Translator mockRoot;
    private Translator translator;

    private ScopeComputer mockScoper;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        translator = new DefaultTranslator(mockRoot);
        mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new FortressOptions(), mockScoper);
    }

    // Convience function to make a PrimSig with a (non-null) parent sig.
    private Sig.PrimSig makePrimSigWithParent(String label, Sig.PrimSig parent) {
        assert parent != null;
        return new Sig.PrimSig(null, label, new Pos("<test>", 0, 0), parent);
    }

    // Alloy test variables are used as placeholders in Alloy test expressions.
    private ExprVar makeTestVariable(String label) {
        return ExprVar.make(null, label);
    }

    private ExprVar makeTestVarWithType(String label, Type type) {
        return ExprVar.make(null, label, type);
    }

    // Convenience function to make a Func representing a predicate.
    private Func makeTestPred(String label, List<Decl> decls, Expr body) {
        return new Func(null, null, label, decls, null, body);
    }

    // Convenience function to make a Func representing a function.
    private Func makeTestFunc(String label, List<Decl> decls, Expr returnExpr, Expr body) {
        return new Func(null, null, label, decls, returnExpr, body);
    }

    // Fortress flag constants are used as mock return values of translations.
    private Var makeFlagConstant(String label) {
        return Term.mkVar(label);
    }

    // For use in Mockito then() with a translate() call: ensure varNames are bound and return "funcName(varNames...)".
    private Answer<Term> useTestFunction(String funcName, String... varNames) {
        return ctx -> {
            // make sure the variable appears in the context
            TranslationContext context = ctx.getArgument(1);
            for (String varName : varNames) {
                assertTrue(context.hasVarMapping(varName));
            }

            // use the mapped vars as arguments to the function
            return Term.mkApp(funcName, Arrays.stream(varNames)
                    .map(context::getVarMapping)
                    .toArray(Var[]::new));
        };
    }

    // Delegate to the real translator for any translation.
    // This should go before other when() calls so it can be overriden for specific arguments.
    // Also, you must use doReturn(...).when(...) for overrides: https://stackoverflow.com/a/34172381.
    private void delegateToRealTranslator() {
        delegateToTranslator(translator);
    }

    // Delegate to the given translator for any translation.
    // Again, you must use doReturn(...).when(...) for overrides.
    private void delegateToTranslator(Translator delegate) {
        when(mockRoot.translate(any(), any())).then(
                ctx -> delegate.translate(ctx.getArgument(0), ctx.getArgument(1)));
    }

    // Assert that a function declaration is a membership predicate for the given sort.
    private void assertIsMembershipPredicate(FuncDecl func, String name) {
        assertThat(func.name(), startsWith(name));
        assertThat(func.arity(), is(1));
        assertThat(func.argSorts().head(), is(context.univSort));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    // Assert that nothing has been added to the context (except the universal sort).
    private void assertContextEmpty(TranslationContext testContext) {
        assertThat(testContext.getTheory(), is(Theory.empty().withSort(testContext.univSort)));
    }

    // Convenience: do it on the global test context
    private void assertContextEmpty() {
        assertContextEmpty(context);
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
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(exactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");

        // scope of univ should be same as scope of the one sig
        assertThat(context.getUnivScope(), is(2));
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
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(nonExactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");

        // scope of univ should be same as scope of the one sig
        assertThat(context.getUnivScope(), is(2));
    }

    @Test
    public void testTranslate_primSig_oneSubsigWithExactScope() {
        // signature with subsig with exact scope
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        Sig.PrimSig child = makePrimSigWithParent("Child", parent);
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
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
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
        assertThat(context.getUnivScope(), is(2));
    }

    @Test
    public void testTranslate_primSig_abstractTwoSubsigsOneExact() {
        // abstract signature with two subsigs, one exact and one not
        Sig.PrimSig parent = new Sig.PrimSig("Parent", Attr.ABSTRACT);
        Sig.PrimSig child1 = makePrimSigWithParent("Child1", parent);
        Sig.PrimSig child2 = makePrimSigWithParent("Child2", parent);
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
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
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
        assertThat(context.getUnivScope(), is(2));
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
    public void testTranslate_field_set() {
        // test "sig A {f: set e}" results in a relation and an axiom [[f in A->e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.setOf());

        // mock out [[f in A->e]]
        Var domainAxiom = makeFlagConstant("domainAxiom");
        when(mockRoot.translate(argThat(isSameAs(f.in(sig.product(e)))), any()))
                .thenReturn(domainAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(domainAxiom));

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_setMultipleArrows() {
        // test "sig A {f: set (e1->e2)}" results in a relation and an axiom [[f in A->e1->e2]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e1 = makeTestVarWithType("e1", Type.make(sig)); // addField() requires it to be typechecked
        Expr e2 = makeTestVarWithType("e2", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e1.product(e2).setOf());

        // mock out [[f in A->e1->e2]]
        Var domainAxiom = makeFlagConstant("domainAxiom");
        when(mockRoot.translate(argThat(isSameAs(f.in(sig.product(e1.product(e2))))), any()))
                .thenReturn(domainAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(3, relationPred.arity()); // arity of A->e1->e2
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(domainAxiom));

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_one() {
        // test "sig A {f: one e}" results in a relation and an axiom [[f in A->one e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.oneOf());

        // mock out [[f in A->one e]]
        Var domainAxiom = makeFlagConstant("domainAxiom");
        when(mockRoot.translate(argThat(isSameAs(f.in(sig.any_arrow_one(e)))), any()))
                .thenReturn(domainAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(domainAxiom));

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_lone() {
        // test "sig A {f: lone e}" results in a relation and an axiom [[f in A->lone e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.loneOf());

        // mock out [[f in A->lone e]]
        Var domainAxiom = makeFlagConstant("domainAxiom");
        when(mockRoot.translate(argThat(isSameAs(f.in(sig.any_arrow_lone(e)))), any()))
                .thenReturn(domainAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(domainAxiom));

        // should have no constants
        assertThat(context.getTheory().constants().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_some() {
        // test "sig A {f: some e}" results in a relation and an axiom [[f in A->some e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.someOf());

        // mock out [[f in A->some e]]
        Var domainAxiom = makeFlagConstant("domainAxiom");
        when(mockRoot.translate(argThat(isSameAs(f.in(sig.any_arrow_some(e)))), any()))
                .thenReturn(domainAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        @SuppressWarnings("unchecked") // IntelliJ gives a false positive
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(domainAxiom));

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
    public void testTranslate_and_noConjuncts() {
        // test that an empty list of 'and' conjuncts translates to Top
        Expr emptyAnd = ExprList.make(null, null, ExprList.Op.AND, new ArrayList<>());
        Term result = translator.translate(emptyAnd, context);
        assertEquals(Term.mkTop(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_and_oneConjunct() {
        // test that [[AND(x)]] := [[x]], where AND(x) denotes an AND ExprList
        ExprVar x = makeTestVariable("x");
        Var flagX = makeFlagConstant("x");
        when(mockRoot.translate(eq(x), any())).thenReturn(flagX);
        Expr andList = ExprList.make(null, null, ExprList.Op.AND, Collections.singletonList(x));
        Term result = translator.translate(andList, context);
        assertEquals(flagX, result);
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
    public void testTranslate_or_noDisjuncts() {
        // test that an empty list of 'or' disjuncts translates to Bottom
        Expr emptyOr = ExprList.make(null, null, ExprList.Op.OR, new ArrayList<>());
        Term result = translator.translate(emptyOr, context);
        assertEquals(Term.mkBottom(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_or_oneDisjunct() {
        // test that [[OR(x)]] := [[x]], where OR(x) denotes an OR ExprList
        ExprVar x = makeTestVariable("x");
        Var flagX = makeFlagConstant("x");
        when(mockRoot.translate(eq(x), any())).thenReturn(flagX);
        Expr orList = ExprList.make(null, null, ExprList.Op.OR, Collections.singletonList(x));
        Term result = translator.translate(orList, context);
        assertEquals(flagX, result);
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
    public void testTranslate_ifThenElse() {
        // test [[a => b else c]] := IfThenElse([[a]], [[b]], [[c]])
        ExprVar a = makeTestVariable("a"), b = makeTestVariable("b"), c = makeTestVariable("c");
        Var flagA = makeFlagConstant("a"), flagB = makeFlagConstant("b"), flagC = makeFlagConstant("c");
        when(mockRoot.translate(eq(a), any())).thenReturn(flagA);
        when(mockRoot.translate(eq(b), any())).thenReturn(flagB);
        when(mockRoot.translate(eq(c), any())).thenReturn(flagC);
        Term result = translator.translate(a.ite(b, c), context);
        assertEquals(Term.mkIfThenElse(flagA, flagB, flagC), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_ifThenElse_expr() {
        // test [[x \in f => e1 else e2]] := IfThenElse([[f]], [[x \in e1]], [[x \in e2]])
        ExprVar f = makeTestVariable("f"), e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var x = Term.mkVar("x");
        ConstList<Var> varList = ConstList.make(Collections.singletonList(x));
        Var flagF = makeFlagConstant("f"), flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(eq(f), any())).thenReturn(flagF);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(varList, e1))), any())).thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(varList, e2))), any())).thenReturn(flagInE2);
        Term result = translator.translate(ExprElementOf.make(varList, f.ite(e1, e2)), context);
        assertEquals(Term.mkIfThenElse(flagF, flagInE1, flagInE2), result);
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
    public void testTranslate_declarationFormula_someSome() {
        // test [[e in A some->some B]] := [[e in A->B]] && [[all a: A | some a.e]] && [[all b: B | some e.b]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        Decl a = A.oneOf("a");
        Decl b = B.oneOf("b");

        // mock out [[e in A->B]]
        Var flagInAToB = makeFlagConstant("inAToB");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B)))), any())).thenReturn(flagInAToB);

        // mock out [[all a: A | some a.e]] and [[all b: B | some e.b]]
        Var flagABound = makeFlagConstant("ABound");
        Var flagBBound = makeFlagConstant("BBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(a.get().join(e).some().forAll(a))), any()))
                .thenReturn(flagABound);
        when(mockRoot.translate(argThat(isAlphaEquivalent(e.join(b.get()).some().forAll(b))), any()))
                .thenReturn(flagBBound);

        Term result = translator.translate(e.in(A.some_arrow_some(B)), context);
        assertEquals(Term.mkAnd(flagInAToB, flagABound, flagBBound), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_declarationFormula_anySome() {
        // test [[e in A->some B]] := [[e in A->B]] && [[all a: A | some a.e]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        Decl a = A.oneOf("a");

        // mock out [[e in A->B]]
        Var flagInAToB = makeFlagConstant("inAToB");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B)))), any())).thenReturn(flagInAToB);

        // mock out [[all a: A | some a.e]]
        Var flagABound = makeFlagConstant("ABound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(a.get().join(e).some().forAll(a))), any()))
                .thenReturn(flagABound);

        Term result = translator.translate(e.in(A.any_arrow_some(B)), context);
        assertEquals(Term.mkAnd(flagInAToB, flagABound), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_declarationFormula_someAny() {
        // test [[e in A some->B]] := [[e in A->B]] && [[all b: B | some e.b]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        Decl b = B.oneOf("b");

        // mock out [[e in A->B]]
        Var flagInAToB = makeFlagConstant("inAToB");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B)))), any())).thenReturn(flagInAToB);

        // mock out [[all b: B | some e.b]]
        Var flagBBound = makeFlagConstant("BBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(e.join(b.get()).some().forAll(b))), any()))
                .thenReturn(flagBBound);

        Term result = translator.translate(e.in(A.some_arrow_any(B)), context);
        assertEquals(Term.mkAnd(flagInAToB, flagBBound), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_declarationFormula_nestedFirst() {
        // test [[e in (A some->some B)->C]] := [[e in (A->B)->C]] && [[all c: C | e.c in A some->some B]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)).product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        ExprVar C = makeTestVarWithType("C", Type.make(sig));
        Decl c = C.oneOf("c");

        // mock out [[e in (A->B)->C]]
        Var flagInArrow = makeFlagConstant("inArrow");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B).product(C)))), any()))
                .thenReturn(flagInArrow);

        // mock out [[all c: C | e.c in A some->some B]]
        Var flagNestedBound = makeFlagConstant("nestedBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                e.join(c.get()).in(A.some_arrow_some(B)).forAll(c))), any())).thenReturn(flagNestedBound);

        Term result = translator.translate(e.in(A.some_arrow_some(B).product(C)), context);
        assertEquals(Term.mkAnd(flagInArrow, flagNestedBound), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_declarationFormula_nestedSecond() {
        // test [[e in A->(B some->some C)]] := [[e in A->(B->C)]] && [[all a: A | a.e in B some->some C]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)).product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        ExprVar C = makeTestVarWithType("C", Type.make(sig));
        Decl a = A.oneOf("a");

        // mock out [[e in A->(B->C)]]
        Var flagInArrow = makeFlagConstant("inArrow");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B.product(C))))), any()))
                .thenReturn(flagInArrow);

        // mock out [[all a: A | a.e in B some->some C]]
        Var flagNestedBound = makeFlagConstant("nestedBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                a.get().join(e).in(B.some_arrow_some(C)).forAll(a))), any())).thenReturn(flagNestedBound);

        Term result = translator.translate(e.in(A.product(B.some_arrow_some(C))), context);
        assertEquals(Term.mkAnd(flagInArrow, flagNestedBound), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_declarationFormula_comprehensive() {
        // test [[e in (A one->B) some->one (C->one D)]] := [[e in (A->B)->(C->D)]] &&
        // [[all a: A one->B | one a.e]] && [[all c: C->one D | some e.c]] &&
        // [[all a: A one->B | a.e in C->one D]] && [[all c: C->one D | e.c in A one->B]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)).product(Type.make(sig))
                .product(Type.make(sig)));
        ExprVar A = makeTestVarWithType("A", Type.make(sig));
        ExprVar B = makeTestVarWithType("B", Type.make(sig));
        ExprVar C = makeTestVarWithType("C", Type.make(sig));
        ExprVar D = makeTestVarWithType("D", Type.make(sig));
        Decl a = A.one_arrow_any(B).oneOf("a");
        Decl c = C.any_arrow_one(D).oneOf("c");

        // mock out [[e in (A->B)->(C->D)]]
        Var flagInArrow = makeFlagConstant("inArrow");
        when(mockRoot.translate(argThat(isSameAs(e.in(A.product(B).product(C.product(D))))), any()))
                .thenReturn(flagInArrow);

        // mock out [[all a: A one->B | one a.e]] and [[all c: C->one D | some e.c]]
        Var flagABound = makeFlagConstant("ABound");
        Var flagCBound = makeFlagConstant("CBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(a.get().join(e).one().forAll(a))), any()))
                .thenReturn(flagABound);
        when(mockRoot.translate(argThat(isAlphaEquivalent(e.join(c.get()).some().forAll(c))), any()))
                .thenReturn(flagCBound);

        // mock out [[all a: A one->B | a.e in C->one D]] and [[all c: C->one D | e.c in A one->B]]
        Var flagANestedBound = makeFlagConstant("ANestedBound");
        Var flagCNestedBound = makeFlagConstant("CNestedBound");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                a.get().join(e).in(C.any_arrow_one(D)).forAll(a))), any())).thenReturn(flagANestedBound);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                e.join(c.get()).in(A.one_arrow_any(B)).forAll(c))), any())).thenReturn(flagCNestedBound);

        Term result = translator.translate(e.in(A.one_arrow_any(B).some_arrow_one(C.any_arrow_one(D))), context);
        assertEquals(Term.mkAnd(flagInArrow, flagABound, flagCBound, flagANestedBound, flagCNestedBound), result);
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
        Var x1 = Term.mkVar("x1_0"), x2 = Term.mkVar("x2_0"), y = Term.mkVar("y0_0");

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
        Var x1 = Term.mkVar("x1_0"), x2 = Term.mkVar("x2_0"), x3 = Term.mkVar("x3_0");
        // match the generated variable names
        Var y1 = Term.mkVar("y0_0"), y2 = Term.mkVar("y1_0");

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
                ExprElementOf.make(Term.mkVar("x"), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

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
                ExprElementOf.make(Term.mkVar("x"), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

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

        // make sure the x mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_sum_oneVar_scope1() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1]
        // where univ has scope 1 and @n is the nth domain element in univ
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        DomainElement domElem = DomainElement.apply(1, context.univSort);
        Term expected = Term.mkIfThenElse(
                Term.mkApp("inE", domElem),
                Term.mkApp("f", domElem),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX), context);
        assertEquals(expected, result);

        // make sure the x mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_sum_oneVar_scope2() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1] + ([[x \in e]] => [[f]] else 0)[x/@2]
        // where univ has scope 2 and @n is the nth domain element in univ
        context.addToUnivScope(2);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        DomainElement domElem1 = DomainElement.apply(1, context.univSort);
        DomainElement domElem2 = DomainElement.apply(2, context.univSort);
        Term expected = Term.mkPlus(
                Term.mkIfThenElse(
                    Term.mkApp("inE", domElem1),
                    Term.mkApp("f", domElem1),
                    IntegerLiteral.apply(0)),
                Term.mkIfThenElse(
                        Term.mkApp("inE", domElem2),
                        Term.mkApp("f", domElem2),
                        IntegerLiteral.apply(0)));
        Term result = translator.translate(f.sumOver(alloyX), context);
        assertEquals(expected, result);

        // make sure the x mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_sum_twoVars_scope1() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@1]
        // where univ has scope 1 and @n is the nth domain element in univ
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0"), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0"), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElem = DomainElement.apply(1, context.univSort);
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(
                        Term.mkApp("inE1", domElem),
                        Term.mkApp("inE2", domElem)),
                Term.mkApp("f", domElem, domElem),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX, alloyY), context);
        assertEquals(expected, result);

        // make sure the mappings were removed
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testTranslate_sum_twoVars_scope2() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@1]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@2]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@2,y/@1]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@2,y/@2]
        // nesting left-to-right, where univ has scope 2 and @n is the nth domain element in univ
        context.addToUnivScope(2);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0"), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0"), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElem1 = DomainElement.apply(1, context.univSort);
        DomainElement domElem2 = DomainElement.apply(2, context.univSort);
        Term expected = Term.mkPlus(
                Term.mkPlus(
                    Term.mkPlus(
                        Term.mkIfThenElse(
                            Term.mkAnd(Term.mkApp("inE1", domElem1), Term.mkApp("inE2", domElem1)),
                            Term.mkApp("f", domElem1, domElem1),
                            IntegerLiteral.apply(0)),
                        Term.mkIfThenElse(
                                Term.mkAnd(Term.mkApp("inE1", domElem1), Term.mkApp("inE2", domElem2)),
                                Term.mkApp("f", domElem1, domElem2),
                                IntegerLiteral.apply(0))),
                    Term.mkIfThenElse(
                            Term.mkAnd(Term.mkApp("inE1", domElem2), Term.mkApp("inE2", domElem1)),
                            Term.mkApp("f", domElem2, domElem1),
                            IntegerLiteral.apply(0))),
                Term.mkIfThenElse(
                        Term.mkAnd(Term.mkApp("inE1", domElem2), Term.mkApp("inE2", domElem2)),
                        Term.mkApp("f", domElem2, domElem2),
                        IntegerLiteral.apply(0)));
        Term result = translator.translate(f.sumOver(alloyX, alloyY), context);
        assertEquals(expected, result);

        // make sure the mappings were removed
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testTranslate_sum_oneVar_int() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1]
        // where the bitwidth is 0 and @n is the nth domain element in Int, and e is of type Int
        when(mockScoper.getBitwidth()).thenReturn(0);
        ExprVar e = makeTestVarWithType("e", Type.make(Sig.SIGINT));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x"), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        DomainElement domElem = DomainElement.apply(1, Sort.Int());
        Term expected = Term.mkIfThenElse(
                Term.mkApp("inE", domElem),
                Term.mkApp("f", domElem),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX), context);
        assertEquals(expected, result);

        // make sure the x mapping was removed
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_sum_mixedIntNonInt() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1u,y/@1i]
        // where univ has scope 1, bitwidth is 0, @1u is the 1st univ domain element, @1i is the 1st Int domain element,
        // e1 is in univ and e2 is in Int
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(Sig.SIGINT));
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestVariable("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0"), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0"), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElemUniv = DomainElement.apply(1, context.univSort);
        DomainElement domElemInt = DomainElement.apply(1, Sort.Int());
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(
                        Term.mkApp("inE1", domElemUniv),
                        Term.mkApp("inE2", domElemInt)),
                Term.mkApp("f", domElemUniv, domElemInt),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX, alloyY), context);
        assertEquals(expected, result);

        // make sure the mappings were removed
        assertFalse(context.hasVarMapping("x"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testTranslate_inSum() {
        // test [[x \in sum y: e | f]] := x = [[sum y: e | f]]
        Var x = Term.mkVar("x");
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e = makeTestVarWithType("e", Type.make(sig));
        Expr f = makeTestVariable("f");
        Expr sum = f.sumOver(e.oneOf("y"));

        Term flagSum = makeFlagConstant("sum");
        when(mockRoot.translate(eq(sum), any())).thenReturn(flagSum);

        Term result = translator.translate(ExprElementOf.make(x, sum), context);
        assertEquals(Term.mkEq(x, flagSum), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_unary_scope1() {
        // test [[#e]] := ([[x0 \in e]] => 1 else 0)[x0/@1]
        // where e is unary, univ has scope 1, and @n is the nth domain element in univ
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x0"), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.get(0));
                });

        DomainElement domElem = DomainElement.apply(1, context.univSort);
        Term expected = Term.mkIfThenElse(Term.mkApp("inE", domElem), IntegerLiteral.apply(1), IntegerLiteral.apply(0));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_binary_scope1() {
        // test [[#e]] := ([[(x0,x1) \in e]] => 1 else 0)[x0/@1,x1/@1]
        // where e is binary, univ has scope 1, and @n is the nth domain element in univ
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(Term.mkVar("x0"), Term.mkVar("x1"))), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.get(0), translated.tuple.get(1));
                });

        DomainElement domElem = DomainElement.apply(1, context.univSort);
        Term expected = Term.mkIfThenElse(Term.mkApp("inE", domElem, domElem),
                IntegerLiteral.apply(1), IntegerLiteral.apply(0));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_binaryWithInt_scope1() {
        // test [[#e]] := ([[(x0,x1) \in e]] => 1 else 0)[x0/@1u,x1/@1i]
        // where e is binary with the second sig being Int, univ has scope 1, @nu is the nth domain element in univ,
        // and @ni is the nth domain element in Int
        context.addToUnivScope(1);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(Sig.SIGINT)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(Term.mkVar("x0"), Term.mkVar("x1"))), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.get(0), translated.tuple.get(1));
                });

        DomainElement domElemUniv = DomainElement.apply(1, context.univSort);
        DomainElement domElemInt = DomainElement.apply(1, Sort.Int());
        Term expected = Term.mkIfThenElse(Term.mkApp("inE", domElemUniv, domElemInt),
                IntegerLiteral.apply(1), IntegerLiteral.apply(0));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_unary_univScope2() {
        // test [[#e]] := ([[x0 \in e]] => 1 else 0)[x0/@1] + ([[x0 \in e]] => 1 else 0)[x0/@2]
        // where e is unary, univ has scope 2, and @n is the nth domain element in univ
        context.addToUnivScope(2);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x0"), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.get(0));
                });

        DomainElement domElem1 = DomainElement.apply(1, context.univSort);
        DomainElement domElem2 = DomainElement.apply(2, context.univSort);
        Term expected = Term.mkPlus(
                Term.mkIfThenElse(Term.mkApp("inE", domElem1), IntegerLiteral.apply(1), IntegerLiteral.apply(0)),
                Term.mkIfThenElse(Term.mkApp("inE", domElem2), IntegerLiteral.apply(1), IntegerLiteral.apply(0)));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_binary_univScope2() {
        // test [[#e]] := ([[(x0,x1) \in e]] => 1 else 0)[x0/@1,x1/@1]
        //   + ([[(x0,x1) \in e]] => 1 else 0)[x0/@1,x1/@2]
        //   + ([[(x0,x1) \in e]] => 1 else 0)[x0/@2,x1/@1]
        //   + ([[(x0,x1) \in e]] => 1 else 0)[x0/@1,x1/@2]
        // where e is binary, univ has scope 2, and @n is the nth domain element in univ, adding left-to-right
        context.addToUnivScope(2);
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(ConstList.make(Arrays.asList(Term.mkVar("x0"), Term.mkVar("x1"))), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.get(0), translated.tuple.get(1));
                });

        DomainElement domElem1 = DomainElement.apply(1, context.univSort);
        DomainElement domElem2 = DomainElement.apply(2, context.univSort);
        Term expected = Term.mkPlus(
                Term.mkPlus(
                        Term.mkPlus(
                            Term.mkIfThenElse(Term.mkApp("inE", domElem1, domElem1),
                                IntegerLiteral.apply(1), IntegerLiteral.apply(0)),
                            Term.mkIfThenElse(Term.mkApp("inE", domElem1, domElem2),
                                IntegerLiteral.apply(1), IntegerLiteral.apply(0))),
                        Term.mkIfThenElse(Term.mkApp("inE", domElem2, domElem1),
                                IntegerLiteral.apply(1), IntegerLiteral.apply(0))),
                    Term.mkIfThenElse(Term.mkApp("inE", domElem2, domElem2),
                            IntegerLiteral.apply(1), IntegerLiteral.apply(0)));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_comprehension_unary() {
        // test [[x \in {y: e | f}]] := [[x \in e]] && [[f]] where y is mapped to x
        Var x = Term.mkVar("x");
        ExprVar e = makeTestVariable("e");
        Decl y = e.oneOf("y");
        ExprVar f = makeTestVariable("f");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(ConstList.make(1, x), e))), any()))
                .thenReturn(flagInE);

        // mock out [[f]] where y is mapped to x
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("y"));
            assertEquals(x, context.getVarMapping("y"));
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(ConstList.make(1, x), f.comprehensionOver(y));
        Term result = translator.translate(comprehension, context);
        assertEquals(Term.mkAnd(flagInE, flagMappedF), result);
        assertContextEmpty(); // should clear context
    }

    @Test
    public void testTranslate_comprehension_binaryDifferentBounds() {
        // test [[(x1, x2) \in {y1: e1, y2: e2 | f}]] := [[x1 \in e1]] && [[x2 \in e2]] && [[f]]
        // where y1 is mapped to x1 and y2 is mapped to x2
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        ExprVar e1 = makeTestVariable("e1");
        ExprVar e2 = makeTestVariable("e2");
        Decl y1 = e1.oneOf("y1");
        Decl y2 = e2.oneOf("y2");
        ExprVar f = makeTestVariable("f");

        // mock out [[x1 \in e1]] and [[x2 \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(ConstList.make(1, x1), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(ConstList.make(1, x2), e2))), any()))
                .thenReturn(flagInE2);

        // mock out [[f]] where y1 is mapped to x1, y2 is mapped to x2
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("y1"));
            assertTrue(context.hasVarMapping("y2"));
            assertEquals(x1, context.getVarMapping("y1"));
            assertEquals(x2, context.getVarMapping("y2"));
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), f.comprehensionOver(y1, y2));
        Term result = translator.translate(comprehension, context);
        assertEquals(Term.mkAnd(flagInE1, flagInE2, flagMappedF), result);
        assertContextEmpty(); // should clear context
    }

    @Test
    public void testTranslate_comprehension_binarySameBound() {
        // test [[(x1, x2) \in {y1, y2: e | f}]] := [[x1 \in e]] && [[x2 \in e]] && [[f]]
        // where y1 is mapped to x1 and y2 is mapped to x2
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        ExprVar e = makeTestVariable("e");
        ExprVar y1 = makeTestVariable("y1"), y2 = makeTestVariable("y2");
        Decl ys = new Decl(null, null, null, null, Arrays.asList(y1, y2), e.oneOf());
        ExprVar f = makeTestVariable("f");

        // mock out [[x1 \in e1]] and [[x2 \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(ConstList.make(1, x1), e))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(ConstList.make(1, x2), e))), any()))
                .thenReturn(flagInE2);

        // mock out [[f]] where y1 is mapped to x1, y2 is mapped to x2
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("y1"));
            assertTrue(context.hasVarMapping("y2"));
            assertEquals(x1, context.getVarMapping("y1"));
            assertEquals(x2, context.getVarMapping("y2"));
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(ConstList.make(Arrays.asList(x1, x2)), f.comprehensionOver(ys));
        Term result = translator.translate(comprehension, context);
        assertEquals(Term.mkAnd(flagInE1, flagInE2, flagMappedF), result);
        assertContextEmpty(); // should clear context
    }

    @Test
    public void testTranslate_someExpr() {
        // test [[some e]] := [[some x: e | true]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // use a custom delegate translator to make sure it's correctly translated
        Var flag = makeFlagConstant("translated");
        delegateToTranslator((expr, context) -> {
            // check that it's "some x: e | true" for some variable x
            if (!(expr instanceof ExprQt)) return null;
            ExprQt qt = (ExprQt) expr;
            boolean correct = qt.op == ExprQt.Op.SOME
                    && qt.decls.size() == 1
                    && qt.decls.get(0).expr.isSame(e.oneOf())
                    && qt.sub == ExprConstant.TRUE;
            return correct ? flag : null;
        });

        Term result = translator.translate(e.some(), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_noExpr() {
        // test [[no e]] := [[no x: e | true]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // use a custom delegate translator to make sure it's correctly translated
        Var flag = makeFlagConstant("translated");
        delegateToTranslator((expr, context) -> {
            // check that it's "no x: e | true" for some variable x
            if (!(expr instanceof ExprQt)) return null;
            ExprQt qt = (ExprQt) expr;
            boolean correct = qt.op == ExprQt.Op.NO
                    && qt.decls.size() == 1
                    && qt.decls.get(0).expr.isSame(e.oneOf())
                    && qt.sub == ExprConstant.TRUE;
            return correct ? flag : null;
        });

        Term result = translator.translate(e.no(), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_loneExpr() {
        // test [[lone e]] := [[lone x: e | true]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // use a custom delegate translator to make sure it's correctly translated
        Var flag = makeFlagConstant("translated");
        delegateToTranslator((expr, context) -> {
            // check that it's "lone x: e | true" for some variable x
            if (!(expr instanceof ExprQt)) return null;
            ExprQt qt = (ExprQt) expr;
            boolean correct = qt.op == ExprQt.Op.LONE
                    && qt.decls.size() == 1
                    && qt.decls.get(0).expr.isSame(e.oneOf())
                    && qt.sub == ExprConstant.TRUE;
            return correct ? flag : null;
        });

        Term result = translator.translate(e.lone(), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_oneExpr() {
        // test [[one e]] := [[one x: e | true]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // use a custom delegate translator to make sure it's correctly translated
        Var flag = makeFlagConstant("translated");
        delegateToTranslator((expr, context) -> {
            // check that it's "one x: e | true" for some variable x
            if (!(expr instanceof ExprQt)) return null;
            ExprQt qt = (ExprQt) expr;
            boolean correct = qt.op == ExprQt.Op.ONE
                    && qt.decls.size() == 1
                    && qt.decls.get(0).expr.isSame(e.oneOf())
                    && qt.sub == ExprConstant.TRUE;
            return correct ? flag : null;
        });

        Term result = translator.translate(e.one(), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_let() {
        // test [[let x = e | f(x)]] := [[f(e)]]
        ExprVar e = makeTestVariable("e");
        ExprVar x = makeTestVariable("x");
        ExprVar f = makeTestVariable("f");

        // make sure the argument is e and the context was saved
        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x"));
            TranslationContext.LetContext letContext = context.getLetMapping("x");
            assertNotNull(letContext);
            assertEquals(e, letContext.getExpr());

            // make sure we saved the correct context (should be empty)
            letContext.useLetMapping();
            assertContextEmpty(context);
            letContext.resetMapping();

            return flag;
        });

        Term result = translator.translate(ExprLet.make(null, x, e, f), context);
        assertEquals(flag, result);

        // make sure x is flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_let_recursion() {
        // test [[let x = x | f]] := [[f]] (and there's no infinite recursion)
        ExprVar x = makeTestVariable("x");
        ExprVar f = makeTestVariable("f");

        delegateToRealTranslator();
        Var flagF = makeFlagConstant("flag");
        doReturn(flagF).when(mockRoot).translate(eq(f), any());

        Term result = translator.translate(ExprLet.make(null, x, x, f), context);
        assertEquals(flagF, result);
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasVarMapping("x"));
    }

    @Test
    public void testTranslate_let_nested() {
        // test [[let a = e | let e = x | a]] := [[e]], not [[x]]
        // this tests that context is saved/restored correctly
        ExprVar a = makeTestVariable("a");
        ExprVar e = makeTestVariable("e");
        ExprVar x = makeTestVariable("x");

        Var fortressE = Term.mkVar("e");
        context.addVarMapping("e", fortressE);
        delegateToRealTranslator();

        Term result = translator.translate(ExprLet.make(null, a, e, ExprLet.make(null, e, x, a)), context);
        assertEquals(fortressE, result);

        // make sure things are flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("a"));
        assertFalse(context.hasVarMapping("a"));
        assertTrue(context.hasVarMapping("e"));
        assertEquals(fortressE, context.getVarMapping("e"));
    }

    @Test
    public void testTranslate_variable_var() {
        // test [[x \in v]] := x = v for an Alloy variable v
        // explicitly set the variable mapping in the context
        ExprVar alloyVar = makeTestVariable("v");
        Var x = Term.mkVar("x");
        Var v = Term.mkVar("v");
        context.addVarMapping(alloyVar.label, v);

        Term result = translator.translate(ExprElementOf.make(x, alloyVar), context);
        assertEquals(Term.mkEq(x, v), result);
    }

    @Test
    public void testTranslate_variable_let() {
        // test [[(x1,x2) \in v]] := [[(x1,x2) \in e]] when in "let v = e" context
        // explicitly set the mapping in the context
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        ExprVar expr = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        ExprVar alloyVar = makeTestVariable("v");
        context.addLetMapping(alloyVar.label, expr);

        // mock out [[(x1,x2) \in e]]
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");
        ConstList<Var> vars = ConstList.make(Arrays.asList(x1, x2));
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(vars, expr))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(ExprElementOf.make(vars, alloyVar), context);
        assertEquals(flagInE, result);
    }

    @Test
    public void testTranslate_pred_nilary() {
        // test [[ p[] ]] := [[f]] when "pred p { f }" is defined
        ExprVar f = makeTestVariable("f");
        Func pred = makeTestPred("p", null, f);

        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).thenReturn(flag);

        Term result = translator.translate(pred.call(), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_pred_unary() {
        // test [[ u[y] ]] := [[f(y)]] when "pred u[x: S] { f(x) }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl xDecl = sig.oneOf("x");
        ExprVar y = makeTestVariable("y");
        ExprVar f = makeTestVariable("f");
        Func pred = makeTestPred("u", Collections.singletonList(xDecl), f);

        // make sure the argument is y
        Term flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x"));
            assertEquals(y, Objects.requireNonNull(context.getLetMapping("x")).getExpr());
            return flag;
        });

        Term result = translator.translate(pred.call(y), context);
        assertEquals(flag, result);

        // make sure y is flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testTranslate_pred_binary() {
        // test [[ b[y1, y2] ]] := [[f(y1, y2)]] when "pred b[x1: S, x2: S] { f(x1, x2) }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl x1Decl = sig.oneOf("x1");
        Decl x2Decl = sig.oneOf("x2");
        ExprVar y1 = makeTestVariable("y1");
        ExprVar y2 = makeTestVariable("y2");
        ExprVar f = makeTestVariable("f");
        Func pred = makeTestPred("b", Arrays.asList(x1Decl, x2Decl), f);

        // make sure the arguments are y1, y2
        Term flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x1"));
            assertTrue(context.hasLetMapping("x2"));
            assertEquals(y1, Objects.requireNonNull(context.getLetMapping("x1")).getExpr());
            assertEquals(y2, Objects.requireNonNull(context.getLetMapping("x2")).getExpr());
            return flag;
        });

        Term result = translator.translate(pred.call(y1, y2), context);
        assertEquals(flag, result);

        // make sure y1, y2 are flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("y1"));
        assertFalse(context.hasLetMapping("y2"));
        assertFalse(context.hasVarMapping("y1"));
        assertFalse(context.hasVarMapping("y2"));
    }

    @Test
    public void testTranslate_fun_nilary() {
        // test [[ x \in g[] ]] := [[x \in f]] when "fun g: S { f }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        ExprVar f = makeTestVariable("f");
        Func fun = makeTestFunc("g", null, sig, f);
        Var x = Term.mkVar("x");
        ConstList<Var> vars = ConstList.make(Collections.singletonList(x));

        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(vars, f))), any()))
                .thenReturn(flag);

        Term result = translator.translate(ExprElementOf.make(vars, fun.call()), context);
        assertEquals(flag, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_fun_unary() {
        // test [[ x \in u[y] ]] := [[f(y)]] when "fun u[x: S]: S { f(x) }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl xDecl = sig.oneOf("x");
        ExprVar y = makeTestVariable("y");
        ExprVar f = makeTestVariable("f");
        Func fun = makeTestFunc("u", Collections.singletonList(xDecl), sig, f);
        Var x = Term.mkVar("x");
        ConstList<Var> vars = ConstList.make(Collections.singletonList(x));

        // make sure the argument is y
        Term flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(vars, f))), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x"));
            assertEquals(y, Objects.requireNonNull(context.getLetMapping("x")).getExpr());
            return flag;
        });

        Term result = translator.translate(ExprElementOf.make(vars, fun.call(y)), context);
        assertEquals(flag, result);

        // make sure y is flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("y"));
        assertFalse(context.hasVarMapping("y"));
    }

    @Test
    public void testTranslate_fun_binary() {
        // test [[ b[y1, y2] ]] := [[f(y1, y2)]] when "fun b[x1: S, x2: S]: S { f(x1, x2) }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl x1Decl = sig.oneOf("x1");
        Decl x2Decl = sig.oneOf("x2");
        ExprVar y1 = makeTestVariable("y1");
        ExprVar y2 = makeTestVariable("y2");
        ExprVar f = makeTestVariable("f");
        Func fun = makeTestFunc("b", Arrays.asList(x1Decl, x2Decl), sig, f);
        Var x = Term.mkVar("x");
        ConstList<Var> vars = ConstList.make(Collections.singletonList(x));

        // make sure the arguments are y1, y2
        Term flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(vars, f))), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x1"));
            assertTrue(context.hasLetMapping("x2"));
            assertEquals(y1, Objects.requireNonNull(context.getLetMapping("x1")).getExpr());
            assertEquals(y2, Objects.requireNonNull(context.getLetMapping("x2")).getExpr());
            return flag;
        });

        Term result = translator.translate(ExprElementOf.make(vars, fun.call(y1, y2)), context);
        assertEquals(flag, result);

        // make sure y1, y2 are flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("y1"));
        assertFalse(context.hasLetMapping("y2"));
        assertFalse(context.hasVarMapping("y1"));
        assertFalse(context.hasVarMapping("y2"));
    }

    @Test
    public void testTranslate_varAsExpression() {
        // test [[x]] := x (as an [integer] expression)
        Var x = Term.mkVar("x");
        context.addVarMapping("x", x);
        Term result = translator.translate(makeTestVariable("x"), context);
        assertEquals(Term.mkVar("x"), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_literal() {
        // test [[2]] := 2 (as an integer literal)
        Term result = translator.translate(ExprConstant.makeNUMBER(2), context);
        assertEquals(IntegerLiteral.apply(2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_inIntLiteral() {
        // test [[x \in 2]] := [[x]] = 2
        delegateToRealTranslator();
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x, ExprConstant.makeNUMBER(2)), context);
        assertEquals(Term.mkEq(x, IntegerLiteral.apply(2)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_quantifyOverInt() {
        // test [[all x: Int | f]] := forall x: Int . true => [[f]]
        // the 'true' is due to skipping the [[x \in Int]] condition
        Decl x = Sig.SIGINT.oneOf("x");
        ExprVar f = makeTestVariable("f");

        Term flagF = makeFlagConstant("flagF");
        AtomicReference<Var> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure x has a mapping here and capture it
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasVarMapping("x"));
            fortressX.set(context.getVarMapping("x"));
            return flagF;
        });

        Term result = translator.translate(f.forAll(x), context);
        assertEquals(Term.mkForall(fortressX.get().of(Sort.Int()), Term.mkImp(Term.mkTop(), flagF)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_inLiterals() {
        // unoptimized: test [[2 in 3]] := forall x: Int . [[x \in 2]] => [[x \in 3]]
        Var x = Term.mkVar("x0_0");

        Term flagIn2 = makeFlagConstant("in2"), flagIn3 = makeFlagConstant("in3");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, ExprConstant.makeNUMBER(2)))), any()))
                .thenReturn(flagIn2);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, ExprConstant.makeNUMBER(3)))), any()))
                .thenReturn(flagIn3);

        Term result = translator.translate(ExprConstant.makeNUMBER(2).in(ExprConstant.makeNUMBER(3)), context);
        assertEquals(Term.mkForall(x.of(Sort.Int()), Term.mkImp(flagIn2, flagIn3)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_eqLiterals() {
        // unoptimized: test [[2 = 3]] := forall x: Int . [[x \in 2]] <=> [[x \in 3]]
        Var x = Term.mkVar("x0_0");

        Term flagIn2 = makeFlagConstant("in2"), flagIn3 = makeFlagConstant("in3");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, ExprConstant.makeNUMBER(2)))), any()))
                .thenReturn(flagIn2);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x, ExprConstant.makeNUMBER(3)))), any()))
                .thenReturn(flagIn3);

        Term result = translator.translate(ExprConstant.makeNUMBER(2).equal(ExprConstant.makeNUMBER(3)), context);
        assertEquals(Term.mkForall(x.of(Sort.Int()), Term.mkIff(flagIn2, flagIn3)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_eqIntVars() {
        // unoptimized: recursively translating,
        // test [[some x: Int | x = 2]] := exists x: Int | true && (forall y: Int | y = x <=> y = 2]])
        // "true" from the lack of a quantification condition for Int
        Decl alloyX = Sig.SIGINT.oneOf("x");
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        delegateToRealTranslator();
        Term result = translator.translate(alloyX.get().equal(ExprConstant.makeNUMBER(2)).forSome(alloyX), context);
        Term expected = Term.mkExists(x.of(Sort.Int()),
                Term.mkAnd(Term.mkTop(),
                        Term.mkForall(y.of(Sort.Int()),
                                Term.mkIff(Term.mkEq(y, x), Term.mkEq(y, IntegerLiteral.apply(2))))));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_binaryComparisonsAndOperations() {
        // test [[2 X 3]] := 2 [[X]] 3 for X a binary comparison or arithmetic operation
        // unfortunately JUnit4 doesn't support parameterized tests...
        List<Pair<ExprBinary.Op, BiFunction<Term, Term, Term>>> alloyToFortressOps = Arrays.asList(
                new Pair<>(ExprBinary.Op.GT, Term::mkGT), // >
                new Pair<>(ExprBinary.Op.NOT_LTE, Term::mkGT), // !=<
                new Pair<>(ExprBinary.Op.GTE, Term::mkGE), // >=
                new Pair<>(ExprBinary.Op.NOT_LT, Term::mkGE), // !<
                new Pair<>(ExprBinary.Op.LT, Term::mkLT), // <
                new Pair<>(ExprBinary.Op.NOT_GTE, Term::mkLT), // !>=
                new Pair<>(ExprBinary.Op.LTE, Term::mkLE), // =<
                new Pair<>(ExprBinary.Op.NOT_GT, Term::mkLE), // !>
                new Pair<>(ExprBinary.Op.IPLUS, Term::mkPlus), // @+ (integer plus)
                new Pair<>(ExprBinary.Op.IMINUS, Term::mkSub), // @- (integer minus)
                new Pair<>(ExprBinary.Op.MUL, Term::mkMult), // *
                new Pair<>(ExprBinary.Op.DIV, Term::mkDiv), // /
                new Pair<>(ExprBinary.Op.REM, Term::mkMod)); // %

        delegateToRealTranslator();
        for (Pair<ExprBinary.Op, BiFunction<Term, Term, Term>> alloyToFortressOp : alloyToFortressOps) {
            ExprBinary.Op alloyOp = alloyToFortressOp.a;
            BiFunction<Term, Term, Term> fortressOp = alloyToFortressOp.b;

            Term result = translator.translate(
                    alloyOp.make(null, null, ExprConstant.makeNUMBER(2), ExprConstant.makeNUMBER(3)), context);
            Term expected = fortressOp.apply(IntegerLiteral.apply(2), IntegerLiteral.apply(3));
            assertEquals(expected, result);
            assertContextEmpty();
        }
    }

    @Test
    public void testTranslate_int_chainedPlus() {
        // test [[2.plus[1].plus[3]]] := (2+1)+3
        delegateToRealTranslator();
        Term result = translator.translate(
                ExprConstant.makeNUMBER(2).iplus(ExprConstant.makeNUMBER(1)).iplus(ExprConstant.makeNUMBER(3)),
                context);
        Term expected = Term.mkPlus(
                Term.mkPlus(IntegerLiteral.apply(2), IntegerLiteral.apply(1)), IntegerLiteral.apply(3));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_binaryOperationExpression_mixedIntNonInt_fails() {
        // test [[S X 2]] fails for select binary operations X, since we disallow mixing integers with non-integers
        Sig.PrimSig sig = new Sig.PrimSig("S");
        List<ExprBinary.Op> binOps = Arrays.asList(
                ExprBinary.Op.IPLUS,
                ExprBinary.Op.IMINUS,
                ExprBinary.Op.MUL,
                ExprBinary.Op.DIV,
                ExprBinary.Op.REM,
                ExprBinary.Op.EQUALS,
                ExprBinary.Op.NOT_EQUALS,
                ExprBinary.Op.IN,
                ExprBinary.Op.NOT_IN,
                ExprBinary.Op.GT,
                ExprBinary.Op.NOT_GT,
                ExprBinary.Op.GTE,
                ExprBinary.Op.NOT_GTE,
                ExprBinary.Op.LT,
                ExprBinary.Op.NOT_LT,
                ExprBinary.Op.LTE,
                ExprBinary.Op.NOT_LTE);
        for (ExprBinary.Op op : binOps) {
            Expr mixedExpr = op.make(null, null, sig, ExprConstant.makeNUMBER(2));
            assertThrows("Should reject mixing integers with non-integers: " + op, ErrorFatal.class,
                    () -> translator.translate(mixedExpr, context));
        }
    }

    @Test
    public void testTranslate_inBinaryOperation_mixedIntNonInt_fails() {
        // test [[x \in S X 2]] fails for select binary operations X, since we disallow mixing ints with non-integers
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Var x = Term.mkVar("x");
        List<ExprBinary.Op> binOps = Arrays.asList(
                ExprBinary.Op.PLUS,
                ExprBinary.Op.MINUS,
                ExprBinary.Op.INTERSECT,
                ExprBinary.Op.JOIN,
                ExprBinary.Op.DOMAIN,
                ExprBinary.Op.RANGE,
                ExprBinary.Op.PLUSPLUS,
                ExprBinary.Op.ARROW);
        for (ExprBinary.Op op : binOps) {
            Expr mixedExpr = ExprElementOf.make(x, op.make(null, null, sig, ExprConstant.makeNUMBER(2)));
            assertThrows("Should reject mixing integers with non-integers: " + op, ErrorFatal.class,
                    () -> translator.translate(mixedExpr, context));
        }
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
        // test [[x \in none]] := false
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x, ExprConstant.EMPTYNESS), context);
        assertEquals(Term.mkBottom(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_true() {
        // test [[true]] := Top
        Term result = translator.translate(ExprConstant.TRUE, context);
        assertEquals(Term.mkTop(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_false() {
        // test [[false]] := Bottom
        Term result = translator.translate(ExprConstant.FALSE, context);
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

    @Test
    public void testTranslate_cast2int() {
        // test cast2int is ignored: [[cast2int(e)]] := [[e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        Term result = translator.translate(ExprUnary.Op.CAST2INT.make(null, e), context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cast2sigint() {
        // test cast2sigint is ignored: [[cast2sigint(e)]] := [[e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        Term result = translator.translate(ExprUnary.Op.CAST2SIGINT.make(null, e), context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inCast2int() {
        // test cast2int is ignored: [[x \in cast2int(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x, ExprUnary.Op.CAST2INT.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inCast2sigint() {
        // test cast2sigint is ignored: [[x \in cast2sigint(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x, e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x, ExprUnary.Op.CAST2SIGINT.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

}
