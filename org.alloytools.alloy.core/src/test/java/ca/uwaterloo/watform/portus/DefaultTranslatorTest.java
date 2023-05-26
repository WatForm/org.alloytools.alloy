package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.App;
import fortress.msfol.DomainElement;
import fortress.msfol.Forall;
import fortress.msfol.FuncDecl;
import fortress.msfol.Iff;
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
import static org.mockito.AdditionalAnswers.delegatesTo;
import static org.mockito.AdditionalMatchers.or;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class DefaultTranslatorTest {

    private final Sort univ = Sort.mkSortConst("testUniv");

    private Translator mockRoot;
    private Translator translator;

    private ScopeComputer mockScoper;
    private TranslationContext context;
    private SortPolicy mockSortPolicy;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        translator = new DefaultTranslator(mockRoot, new QuantifierScopeAxiomStrategy());
        // Use the constructor so RangeAssigner's list of sigs isn't null (causes issues with copy constructor)
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        mockScoper = mock(ScopeComputer.class);
        mockSortPolicy = mock(SortPolicy.class, delegatesTo(
                new UnivSortPolicy(univ, Collections.emptyList(), mockScoper)));
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    // Convience function to make a PrimSig with a (non-null) parent sig.
    private Sig.PrimSig makePrimSigWithParent(String label, Sig.PrimSig parent) {
        assert parent != null;
        return new Sig.PrimSig(null, label, new Pos("<test>", 0, 0), parent);
    }

    // Alloy test variables are used as placeholders in Alloy test expressions.
    private ExprVar makeTestVariable(String label) {
        return ExprVar.make(null, label, Type.make(new Sig.PrimSig("testSort_" + label)));
    }

    private ExprVar makeTestFormulaVar(String label) {
        return ExprVar.make(null, label, Type.FORMULA);
    }

    // Uses Alloy's "small int type", should be used when an int is expected.
    private ExprVar makeTestSmallIntVar(String label) {
        return ExprVar.make(null, label, Type.smallIntType());
    }

    // Uses Alloy's Int sig, should be used when a set is expected.
    private ExprVar makeTestSigIntVar(String label) {
        return ExprVar.make(null, label, Type.make(Sig.SIGINT));
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
                assertTrue(context.hasTermMapping(varName));
            }

            // use the mapped vars as arguments to the function
            //noinspection ConstantConditions - we just checked that they all exist
            return Term.mkApp(funcName, Arrays.stream(varNames)
                    .map(context::getTermMapping)
                    .map(AnnotatedTerm::getTerm)
                    .toArray(Term[]::new));
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
        assertThat(func.argSorts().head(), is(univ));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    // Assert that nothing has been added to the context (except the universal sort).
    private void assertContextEmpty(TranslationContext testContext) {
        assertThat(testContext.getTheory(), is(Theory.empty().withSort(univ)));
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y.of(univ), sig))), any()))
                .thenReturn(inSigFlag);

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // create the expected exact scope axiom
        // "exists x1, x2: univ . forall y: univ . !(x1 = x2) && ([[y \in S]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term exactScopeAxiom = Term.mkExists(Arrays.asList(x1.of(univ), x2.of(univ)),
                Term.mkForall(y.of(univ), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkIff(inSigFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // this should be the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(exactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");
    }

    @Test
    public void testTranslate_primSig_singleNonExactScope() {
        // single signature
        Sig.PrimSig sig = new Sig.PrimSig("TestSig");
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(false);

        // mock out the non-exact scope axiom's [[xi \in sig]]
        Expr inSig = ExprElementOf.make(Term.mkVar("x").of(univ), sig);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inSig)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.getTerm(0)));

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // create the expected non-exact scope axiom
        // "forall x0, x1, x2: univ . [[x0 \in S]] && [[x1 \in S]] && [[x2 \in S]] =>
        // x0 = x1 || x0 = x2 || x1 = x2"
        Var x0 = Term.mkVar("x0");
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term nonExactScopeAxiom = Term.mkForall(
                Arrays.asList(x0.of(univ), x1.of(univ), x2.of(univ)),
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
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(nonExactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");
    }

    @Test
    public void testTranslate_primSig_singleNonExactScope_abstractWithNoChildren() {
        // An abstract signature with no children is not treated as abstract
        Sig.PrimSig sig = new Sig.PrimSig("TestSig", Attr.ABSTRACT);
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(false);

        // mock out the non-exact scope axiom's [[xi \in sig]]
        Expr inSig = ExprElementOf.make(Term.mkVar("x").of(univ), sig);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inSig)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.getTerm(0)));

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // create the expected non-exact scope axiom
        // "forall x0, x1, x2: univ . [[x0 \in S]] && [[x1 \in S]] && [[x2 \in S]] =>
        // x0 = x1 || x0 = x2 || x1 = x2"
        Var x0 = Term.mkVar("x0");
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Term nonExactScopeAxiom = Term.mkForall(
                Arrays.asList(x0.of(univ), x1.of(univ), x2.of(univ)),
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
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(isAlphaEquivalentTerm(nonExactScopeAxiom)));

        // should have no constants, one function for the membership predicate
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl func = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(func, "inTestSig");
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

        // mock out the subset axiom's [[child in parent]]
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = child.in(parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // mock out the exact scope axiom's [[x \in child]] and [[x \in parent]]
        Term inChildFlag = makeFlagConstant("xInChild");
        Expr inChild = ExprElementOf.make(Term.mkVar("x").of(univ), child);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any()))
                .thenReturn(inChildFlag);
        Term inParentFlag = makeFlagConstant("xInParent");
        Expr inParent = ExprElementOf.make(Term.mkVar("x").of(univ), parent);
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
        Term exactScopeAxiom1 = Term.mkExists(Arrays.asList(x1.of(univ), x2.of(univ)),
                Term.mkForall(y.of(univ), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkIff(inParentFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // create the expected exact scope axiom for the child
        // scope 1: "exists x: univ . forall y: univ . [[y \in Child]] <=> y = x"
        Term exactScopeAxiom2 = Term.mkExists(x1.of(univ),
                Term.mkForall(y.of(univ), Term.mkIff(
                        inChildFlag, Term.mkEq(y, x1))));

        // should have two axioms: subset and exact scope
        //noinspection unchecked
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
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
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
        Expr subsetAxiom = child1.in(parent); // doesn't matter which child due to alpha-equivalence
        // this generates flag constants like "subset_Child1"
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any())).then(
                ctx -> {
                    ExprBinary expr = ctx.getArgument(0);
                    Expr child = expr.left;
                    return makeFlagConstant("subset_" + child.toString());
                });

        // mock out the abstract/cover axiom
        Decl xParent = parent.oneOf("x");
        // all x: parent | x in child1 or x in child2
        Expr coverAxiom = xParent.get().in(child1).or(xParent.get().in(child2)).forAll(xParent);
        Term coverFlag = makeFlagConstant("cover");
        when(mockRoot.translate(argThat(isAlphaEquivalent(coverAxiom)), any()))
                .thenReturn(coverFlag);

        // mock out the exact and non-exact scope axiom's [[xi \in sig]]
        Expr inChild = ExprElementOf.make(Term.mkVar("x").of(univ), child1);
        Expr inParent = ExprElementOf.make(Term.mkVar("x").of(univ), parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(inChild)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.getTerm(0)));
        when(mockRoot.translate(argThat(isAlphaEquivalent(inParent)), any())).then(
                ctx -> makeFlagConstant("inFlag_" + ctx.<ExprElementOf>getArgument(0).tuple.getTerm(0)));

        // delegate to the method under test to translate the child sigs
        when(mockRoot.translate(or(eq(child1), eq(child2)), any())).then(
                ctx -> translator.translate(ctx.getArgument(0), ctx.getArgument(1)));

        // actually translate
        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // create the expected disjoint axiom
        Var x = Term.mkVar("x");
        Term disjointnessAxiom = Term.mkForall(x.of(univ),
                Term.mkNot(Term.mkAnd(makeFlagConstant("inFlag_x_0"), makeFlagConstant("inFlag_x_0"))));

        // create the expected exact scope axiom for the parent
        // "exists x1, x2: univ . forall y: univ . !(x1 = x2) && ([[y \in S]] <=> y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var y = Term.mkVar("y");
        Term exactScopeAxiom1 = Term.mkExists(Arrays.asList(x1.of(univ), x2.of(univ)),
                Term.mkForall(y.of(univ), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        // use 'x' since it's the variable name they use
                        Term.mkIff(makeFlagConstant("inFlag_x"), Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // create the expected exact scope axiom for the child
        // "exists x1: univ . forall x: univ . [[x \in child1]] <=> x = x1"
        Term exactScopeAxiom2 = Term.mkExists(x1.of(univ), Term.mkForall(x.of(univ),
                Term.mkIff(makeFlagConstant("inFlag_x"), Term.mkEq(x, x1))));

        // create the expected non-exact scope axiom for the child
        // "forall x0, x1: univ . [[x0 \in child2]] && [[x1 \in child2]] => x0 = x1"
        Var x0 = Term.mkVar("x0");
        Term nonExactScopeAxiom = Term.mkForall(Arrays.asList(x0.of(univ), x1.of(univ)),
                Term.mkImp(
                        Term.mkAnd(
                                makeFlagConstant("inFlag_x0"),
                                makeFlagConstant("inFlag_x1")),
                        Term.mkEq(x0, x1)));

        // should have exactly these axioms
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(makeFlagConstant("subset_Child1")), // subset axiom, child1
                is(makeFlagConstant("subset_Child2")), // subset axiom, child2
                is(coverFlag), // cover/abstract axiom
                isAlphaEquivalentTerm(disjointnessAxiom), // disjoint axiom
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
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_subsetSig_oneParentExactScope() {
        // subset signature "sig B in A {}" where A is a top-level primitive signature
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        when(mockScoper.sig2scope(parent)).thenReturn(2);
        when(mockScoper.isExact(parent)).thenReturn(true);
        Sig.SubsetSig sig = new Sig.SubsetSig(null, "SubsetSig", null, Collections.singletonList(parent));
        when(mockScoper.sig2scope(sig)).thenReturn(1);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // mock out the subset axiom's [[child in parent]]
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = sig.in(parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // actually translate
        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue()));

        // should have just the subset axiom (subset sigs have no scope axioms)
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(is(subsetFlag)));

        // should have the membership predicate
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSubsetSig");
    }

    @Test
    public void testTranslate_subsetSig_twoParentsExactScope() {
        // subset signature "sig C in A + B {}" where A and B are top-level primitive signature
        Sig.PrimSig parent1 = new Sig.PrimSig("Parent1");
        when(mockScoper.sig2scope(parent1)).thenReturn(2);
        when(mockScoper.isExact(parent1)).thenReturn(true);
        Sig.PrimSig parent2 = new Sig.PrimSig("Parent2");
        when(mockScoper.sig2scope(parent2)).thenReturn(2);
        when(mockScoper.isExact(parent2)).thenReturn(true);
        Sig.SubsetSig sig = new Sig.SubsetSig(null, "SubsetSig", null, Arrays.asList(parent1, parent2));
        when(mockScoper.sig2scope(sig)).thenReturn(1);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // mock out the subset axiom's [[child in parent1 + parent2]]
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = sig.in(parent1.plus(parent2));
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // actually translate
        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue()));

        // should have just the subset axiom (subset sigs have no scope axioms)
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(is(subsetFlag)));

        // should have the membership predicate
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSubsetSig");
    }

    @Test
    public void testTranslate_subsetSigEquals_oneParentExactScope() {
        // subset signature "sig B = A {}" where A is a top-level primitive signature
        Sig.PrimSig parent = new Sig.PrimSig("Parent");
        when(mockScoper.sig2scope(parent)).thenReturn(2);
        when(mockScoper.isExact(parent)).thenReturn(true);
        Sig.SubsetSig sig = new Sig.SubsetSig(
                null, "SubsetSig", null, Collections.singletonList(parent), Attr.EXACT);
        when(mockScoper.sig2scope(sig)).thenReturn(1);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // mock out the subset axiom's [[child = parent]]
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = sig.equal(parent);
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // actually translate
        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue()));

        // should have just the subset axiom (subset sigs have no scope axioms)
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(is(subsetFlag)));

        // should have the membership predicate
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSubsetSig");
    }

    @Test
    public void testTranslate_subsetSigEqual_twoParentsExactScope() {
        // subset signature "sig C = A + B {}" where A and B are top-level primitive signature
        Sig.PrimSig parent1 = new Sig.PrimSig("Parent1");
        when(mockScoper.sig2scope(parent1)).thenReturn(2);
        when(mockScoper.isExact(parent1)).thenReturn(true);
        Sig.PrimSig parent2 = new Sig.PrimSig("Parent2");
        when(mockScoper.sig2scope(parent2)).thenReturn(2);
        when(mockScoper.isExact(parent2)).thenReturn(true);
        Sig.SubsetSig sig = new Sig.SubsetSig(
                null, "SubsetSig", null, Arrays.asList(parent1, parent2), Attr.EXACT);
        when(mockScoper.sig2scope(sig)).thenReturn(1);
        when(mockScoper.isExact(sig)).thenReturn(true);

        // mock out the subset axiom's [[child in parent1 + parent2]]
        Term subsetFlag = makeFlagConstant("subset");
        Expr subsetAxiom = sig.equal(parent1.plus(parent2));
        when(mockRoot.translate(argThat(isAlphaEquivalent(subsetAxiom)), any()))
                .thenReturn(subsetFlag);

        // actually translate
        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue()));

        // should have just the subset axiom (subset sigs have no scope axioms)
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, contains(is(subsetFlag)));

        // should have the membership predicate
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSubsetSig");
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
        Term result = translator.translate(ExprElementOf.make(var.of(univ), sig), context);

        // get the membership predicate, should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl inSigPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inSigPred, "inSig");

        // result must be inSig(v)
        assertEquals(Term.mkApp(inSigPred.name(), var), result);
    }

    @Test
    public void testTranslate_field_set() {
        // test "sig A {f: set e}" results in a relation and the proper bound axiom
        Sig.PrimSig sig = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sig)).thenReturn(univ);
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.setOf());

        // mock out the parts of the bound axiom
        Var rangeAxiom = makeFlagConstant("rangeAxiom");
        // [[all this: A | this.f in set e]]
        Expr expectedRangeAxiom = f.sig.decl.get().join(f).in(e.setOf()).forAll(f.sig.decl);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expectedRangeAxiom)), any()))
                .thenReturn(rangeAxiom);
        Var inF = makeFlagConstant("inF");
        AnnotatedVar x0 = Term.mkVar("x_0").of(univ), x1 = Term.mkVar("x_1").of(univ);
        // (x0,x1) \in f
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x0, x1), f))), any()))
                .thenReturn(inF);
        // x0 \in A
        Var inA = makeFlagConstant("inA");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x0, sig))), any()))
                .thenReturn(inA);
        // forall x0: sort, x1: sort . [[(x0, x1) \in f]] => [[x0 \in A]]
        Term domainAxiom = Term.mkForall(Arrays.asList(x0, x1), Term.mkImp(inF, inA));
        Term boundAxiom = Term.mkAnd(domainAxiom, rangeAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the domain axiom is the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(boundAxiom));

        // should have no constants
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_setMultipleArrows() {
        // test "sig A {f: set (e1->e2)}" results in a relation and an axiom [[f in A->e1->e2]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e1 = makeTestVarWithType("e1", Type.make(sig)); // addField() requires it to be typechecked
        Expr e2 = makeTestVarWithType("e2", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e1.product(e2).setOf());

        // mock out the parts of the bound axiom
        Var rangeAxiom = makeFlagConstant("rangeAxiom");
        // [[all this: A | this.f in set e1->e2]]
        Expr expectedRangeAxiom = f.sig.decl.get().join(f).in(e1.product(e2).setOf()).forAll(f.sig.decl);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expectedRangeAxiom)), any()))
                .thenReturn(rangeAxiom);
        Var inF = makeFlagConstant("inF");
        AnnotatedVar x0 = Term.mkVar("x_0").of(univ), x1 = Term.mkVar("x_1").of(univ), x2 = Term.mkVar("x_2").of(univ);
        // (x0,x1,x2) \in f
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x0, x1, x2), f))), any()))
                .thenReturn(inF);
        // x0 \in A
        Var inA = makeFlagConstant("inA");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x0, sig))), any()))
                .thenReturn(inA);
        // forall x0: sort, x1: sort, x2: sort . [[(x0, x1, x2) \in f]] => [[x0 \in A]]
        Term domainAxiom = Term.mkForall(Arrays.asList(x0, x1, x2), Term.mkImp(inF, inA));
        Term boundAxiom = Term.mkAnd(domainAxiom, rangeAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(3, relationPred.arity()); // arity of A->e1->e2
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the bound axiom is the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(boundAxiom));

        // should have no constants
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_one() {
        // test "sig A {f: one e}" results in a relation and an axiom [[f in A->one e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.oneOf());

        // mock out the parts of the bound axiom
        Var rangeAxiom = makeFlagConstant("rangeAxiom");
        // [[all this: A | this.f in one e]]
        Expr expectedRangeAxiom = f.sig.decl.get().join(f).in(e.oneOf()).forAll(f.sig.decl);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expectedRangeAxiom)), any()))
                .thenReturn(rangeAxiom);
        Var inF = makeFlagConstant("inF");
        AnnotatedVar x0 = Term.mkVar("x_0").of(univ), x1 = Term.mkVar("x_1").of(univ);
        // (x0,x1) \in f
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x0, x1), f))), any()))
                .thenReturn(inF);
        // x0 \in A
        Var inA = makeFlagConstant("inA");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x0, sig))), any()))
                .thenReturn(inA);
        // forall x0: sort, x1: sort . [[(x0, x1) \in f]] => [[x0 \in A]]
        Term domainAxiom = Term.mkForall(Arrays.asList(x0, x1), Term.mkImp(inF, inA));
        Term boundAxiom = Term.mkAnd(domainAxiom, rangeAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the bound axiom is the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(boundAxiom));

        // should have no constants
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_lone() {
        // test "sig A {f: lone e}" results in a relation and an axiom [[f in A->lone e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.loneOf());

        // mock out the parts of the bound axiom
        Var rangeAxiom = makeFlagConstant("rangeAxiom");
        // [[all this: A | this.f in one e]]
        Expr expectedRangeAxiom = f.sig.decl.get().join(f).in(e.loneOf()).forAll(f.sig.decl);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expectedRangeAxiom)), any()))
                .thenReturn(rangeAxiom);
        Var inF = makeFlagConstant("inF");
        AnnotatedVar x0 = Term.mkVar("x_0").of(univ), x1 = Term.mkVar("x_1").of(univ);
        // (x0,x1) \in f
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x0, x1), f))), any()))
                .thenReturn(inF);
        // x0 \in A
        Var inA = makeFlagConstant("inA");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x0, sig))), any()))
                .thenReturn(inA);
        // forall x0: sort, x1: sort . [[(x0, x1) \in f]] => [[x0 \in A]]
        Term domainAxiom = Term.mkForall(Arrays.asList(x0, x1), Term.mkImp(inF, inA));
        Term boundAxiom = Term.mkAnd(domainAxiom, rangeAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the bound axiom is the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(boundAxiom));

        // should have no constants
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_field_some() {
        // test "sig A {f: some e}" results in a relation and an axiom [[f in A->some e]]
        Sig.PrimSig sig = new Sig.PrimSig("A");
        Expr e = makeTestVarWithType("e", Type.make(sig)); // addField() requires it to be typechecked
        Sig.Field f = sig.addField("f", e.someOf());

        // mock out the parts of the bound axiom
        Var rangeAxiom = makeFlagConstant("rangeAxiom");
        // [[all this: A | this.f in one e]]
        Expr expectedRangeAxiom = f.sig.decl.get().join(f).in(e.someOf()).forAll(f.sig.decl);
        when(mockRoot.translate(argThat(isAlphaEquivalent(expectedRangeAxiom)), any()))
                .thenReturn(rangeAxiom);
        Var inF = makeFlagConstant("inF");
        AnnotatedVar x0 = Term.mkVar("x_0").of(univ), x1 = Term.mkVar("x_1").of(univ);
        // (x0,x1) \in f
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x0, x1), f))), any()))
                .thenReturn(inF);
        // x0 \in A
        Var inA = makeFlagConstant("inA");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x0, sig))), any()))
                .thenReturn(inA);
        // forall x0: sort, x1: sort . [[(x0, x1) \in f]] => [[x0 \in A]]
        Term domainAxiom = Term.mkForall(Arrays.asList(x0, x1), Term.mkImp(inF, inA));
        Term boundAxiom = Term.mkAnd(domainAxiom, rangeAxiom);

        Term result = translator.translate(f, context);
        assertThat(result, is(notNullValue()));

        // get the relation predicate, it should be the only function
        assertThat(context.getTheory().functionDeclarations().size(), is(1));
        FuncDecl relationPred = context.getTheory().functionDeclarations().head();
        assertEquals("f_0", relationPred.name());
        assertEquals(2, relationPred.arity());
        assertEquals(Sort.Bool(), relationPred.resultSort());

        // make sure the bound axiom is the only axiom
        //noinspection unchecked
        Set<Term> axioms = CollectionConverters.<Term>asJava(context.getTheory().axioms());
        assertThat(axioms, containsInAnyOrder(boundAxiom));

        // should have no constants
        assertThat(context.getTheory().constantDeclarations().size(), is(0));
        assertThat(context.getTheory().enumConstants().size(), is(0));
    }

    @Test
    public void testTranslate_and_twoConjuncts() {
        // test [[x1 and x2]] := [[x1]] && [[x2]]
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2");
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
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2"),
                x3 = makeTestFormulaVar("x3");
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
        ExprVar x = makeTestFormulaVar("x");
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
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2");
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
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2"),
                x3 = makeTestFormulaVar("x3");
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
        ExprVar x = makeTestFormulaVar("x");
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
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2");
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
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2");
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
        ExprVar x = makeTestFormulaVar("x");
        Var flagX = makeFlagConstant("x");
        when(mockRoot.translate(eq(x), any())).thenReturn(flagX);
        Term result = translator.translate(x.not(), context);
        assertEquals(Term.mkNot(flagX), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_ifThenElse() {
        // test [[a => b else c]] := IfThenElse([[a]], [[b]], [[c]])
        ExprVar a = makeTestFormulaVar("a"), b = makeTestFormulaVar("b"), c = makeTestFormulaVar("c");
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
        ExprVar f = makeTestFormulaVar("f"), e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var x = Term.mkVar("x");
        Var flagF = makeFlagConstant("f"), flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(eq(f), any())).thenReturn(flagF);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any())).thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any())).thenReturn(flagInE2);
        Term result = translator.translate(ExprElementOf.make(x.of(univ), f.ite(e1, e2)), context);
        assertEquals(Term.mkIfThenElse(flagF, flagInE1, flagInE2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_union_twoSets() {
        // test [[x \in e1 + e2]] := [[x \in e1]] || [[x \in e2]]
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var flag1 = makeFlagConstant("xInE1"), flag2 = makeFlagConstant("xInE2");
        Var x = makeFlagConstant("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.plus(e2)), context);
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
        doReturn(flag1).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any());
        doReturn(flag2).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any());
        doReturn(flag3).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e3))), any());

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.plus(e2).plus(e3)), context);

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
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.intersect(e2)), context);
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
        doReturn(flag1).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any());
        doReturn(flag2).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any());
        doReturn(flag3).when(mockRoot).translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e3))), any());

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.intersect(e2).intersect(e3)), context);

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
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flag1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e2))), any()))
                .thenReturn(flag2);
        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.minus(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(y.of(univ), x.of(univ)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(univ), Term.mkAnd(flagInE1, flagInE2));
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
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y.of(univ), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(univ), Term.mkAnd(flagInE1, flagInE2));
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
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), y.of(univ)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(y.of(univ), x2.of(univ)), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(univ), Term.mkAnd(flagInE1, flagInE2));
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(y.of(univ), x1.of(univ), x2.of(univ)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1.join(e2)), context);
        Term expected = Term.mkExists(y.of(univ), Term.mkAnd(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_join_oneIndeterminate() {
        // test [[x \in univ . e]] := exists y: univ . [[y \in univ]] && [[(y, x) \in e]]
        // where arity(e2) = 2, because univ has an indeterminate sort
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[y \in e1]] and [[(y, x) \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(y.of(univ), Sig.UNIV))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(y.of(univ), x.of(univ)), e))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), Sig.UNIV.join(e)), context);
        Term expected = Term.mkExists(y.of(univ), Term.mkAnd(flagInE1, flagInE2));
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1.product(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x2.of(univ), x3.of(univ)), e1))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1.product(e2)), context);
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
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x3.of(univ), e1))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1.product(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.domain(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1.domain(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.range(e2)), context);
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
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x1.of(univ), e2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1.range(e2)), context);
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
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1.plus(e2)))), any()))
                .thenReturn(flagUnion);

        Term result = translator.translate(ExprElementOf.make(x.of(univ), e1.override(e2)), context);
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
        // note: use y1 to match the generated variable name for more robust testing
        Var x1 = Term.mkVar("x1_0"), x2 = Term.mkVar("x2_0"), y = Term.mkVar("y1_0");

        // mock out all the element-of checks
        Var flagBothInE1 = makeFlagConstant("bothInE1");
        Var flagBothInE2 = makeFlagConstant("bothInE2");
        Var flagX1InE2 = makeFlagConstant("x1InE2");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1))), any()))
                .thenReturn(flagBothInE1);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e2))), any()))
                .thenReturn(flagBothInE2);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), y.of(univ)), e2))), any()))
                .thenReturn(flagX1InE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1.override(e2)), context);
        Term expected = Term.mkOr(flagBothInE2, Term.mkAnd(
                flagBothInE1, Term.mkNot(Term.mkExists(y.of(univ), flagX1InE2))));
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
        Var y1 = Term.mkVar("y1_0"), y2 = Term.mkVar("y2_0");

        // mock out all the element-of checks
        Var flagAllInE1 = makeFlagConstant("allInE1");
        Var flagAllInE2 = makeFlagConstant("allInE2");
        Var flagX1InE2 = makeFlagConstant("x1InE2");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1))), any()))
                .thenReturn(flagAllInE1);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e2))), any()))
                .thenReturn(flagAllInE2);
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), y1.of(univ), y2.of(univ)), e2))), any()))
                .thenReturn(flagX1InE2);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ), x3.of(univ)), e1.override(e2)), context);
        Term expected = Term.mkOr(flagAllInE2, Term.mkAnd(
                flagAllInE1, Term.mkNot(Term.mkExists(
                        Arrays.asList(y1.of(univ), y2.of(univ)), flagX1InE2))));
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

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.in(e2), context);
        Term expected = Term.mkForall(x.of(univ), Term.mkImp(flagInE1, flagInE2));
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
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.in(e2), context);
        Term expected = Term.mkForall(Arrays.asList(x1.of(univ), x2.of(univ)),
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

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.equal(e2), context);
        Term expected = Term.mkForall(x.of(univ), Term.mkIff(flagInE1, flagInE2));
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
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        Term result = translator.translate(e1.equal(e2), context);
        Term expected = Term.mkForall(Arrays.asList(x1.of(univ), x2.of(univ)),
                Term.mkIff(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inOneOf() {
        // test [[e1 in ONEOF(e2)]] := (forall x: univ . [[x \in ONEOF(e1)]] => [[x \in e2]]) && [[one ONEOF(e2)]]
        // there's some unnecessary mult wrapping, but they're treated like noops so it's fine
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var flagOneE2 = makeFlagConstant("oneE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e2.oneOf()))), any()))
                .thenReturn(flagInE2);
        when(mockRoot.translate(argThat(isSameAs(e2.oneOf().one())), any()))
                .thenReturn(flagOneE2);

        Term result = translator.translate(e1.in(e2.oneOf()), context);
        Term expected = Term.mkAnd(Term.mkForall(x.of(univ), Term.mkImp(flagInE1, flagInE2)), flagOneE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inLoneOf() {
        // test [[e1 in LONEOF(e2)]] := (forall x: univ . [[x \in LONEOF(e1)]] => [[x \in e2]]) && [[lone LONEOF(e2)]]
        // there's some unnecessary mult wrapping, but they're treated like noops so it's fine
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var flagLoneE2 = makeFlagConstant("loneE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e2.loneOf()))), any()))
                .thenReturn(flagInE2);
        when(mockRoot.translate(argThat(isSameAs(e2.loneOf().lone())), any()))
                .thenReturn(flagLoneE2);

        Term result = translator.translate(e1.in(e2.loneOf()), context);
        Term expected = Term.mkAnd(Term.mkForall(x.of(univ), Term.mkImp(flagInE1, flagInE2)), flagLoneE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inSomeOf() {
        // test [[e1 in SOMEOF(e2)]] := (forall x: univ . [[x \in LONEOF(e1)]] => [[x \in e2]]) && [[some SOMEOF(e2)]]
        // there's some unnecessary mult wrapping, but they're treated like noops so it's fine
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var flagSomeE2 = makeFlagConstant("someE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e2.someOf()))), any()))
                .thenReturn(flagInE2);
        when(mockRoot.translate(argThat(isSameAs(e2.someOf().some())), any()))
                .thenReturn(flagSomeE2);

        Term result = translator.translate(e1.in(e2.someOf()), context);
        Term expected = Term.mkAnd(Term.mkForall(x.of(univ), Term.mkImp(flagInE1, flagInE2)), flagSomeE2);
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inSetOf_normal() {
        // test [[e1 in SETOF(e2)]] := forall x: univ . [[x \in SETOF(e1)]] => [[x \in e2]], like normal
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e2.setOf()))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(e1.in(e2.setOf()), context);
        Term expected = Term.mkForall(x.of(univ), Term.mkImp(flagInE1, flagInE2));
        assertThat(result, isAlphaEquivalentTerm(expected));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inExactlyOf() {
        // test [[e1 in EXACTLYOF(e2)]] := forall x: univ . [[x \in EXACTLY(e1)]] <=> [[x \in e2]], like equals
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Expr exactlyE2 = ExprUnary.Op.EXACTLYOF.make(null, e2);
        Var flagInE1 = makeFlagConstant("xInE1"), flagInE2 = makeFlagConstant("xInE2");
        Var x = Term.mkVar("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x.of(univ), exactlyE2))), any()))
                .thenReturn(flagInE2);

        Term result = translator.translate(e1.equal(exactlyE2), context);
        Term expected = Term.mkForall(x.of(univ), Term.mkIff(flagInE1, flagInE2));
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
                ExprElementOf.make(TermTuple.fromVars(x2.of(univ), x1.of(univ)), e))), any()))
                .thenReturn(flagSwapped);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), e.transpose()), context);
        assertEquals(flagSwapped, result);
    }

    @Test
    public void testTranslate_transitiveClosure_relationExists() {
        // test [[(x,y) \in ^f]] := Closure(f(x,y)) if f already exists
        // prime the relation by translating a field f
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field fieldF = sig.addField("f", sig); // f is of type S->S
        translator.translate(fieldF, context);

        // figure out what its relation was
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl funcF = context.getTheory().functionDeclarations().head();

        // test the actual translation
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), fieldF.closure()), context);
        assertEquals(Term.mkClosure(funcF.name(), x, y), result);

        // ensure no relation was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_reflexiveClosure_relationExists() {
        // test [[(x,y) \in *f]] := ReflexiveClosure(f(x,y)) if f already exists
        // prime the relation by translating a field f
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field fieldF = sig.addField("f", sig); // f is of type S->S
        translator.translate(fieldF, context);

        // figure out what its relation was
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl funcF = context.getTheory().functionDeclarations().head();

        // test the actual translation
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), fieldF.reflexiveClosure()), context);
        assertEquals(Term.mkReflexiveClosure(funcF.name(), x, y), result);

        // ensure no relation was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_transitiveClosure_relationExistsWithNoop() {
        // test [[(x,y) \in ^NOOP(f)]] := Closure(f(x,y)) if f already exists
        // prime the relation by translating a field f
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field fieldF = sig.addField("f", sig); // f is of type S->S
        translator.translate(fieldF, context);

        // figure out what its relation was
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl funcF = context.getTheory().functionDeclarations().head();

        // test the actual translation
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)),
                        ExprUnary.Op.NOOP.make(null, fieldF).closure()), context);
        assertEquals(Term.mkClosure(funcF.name(), x, y), result);

        // ensure no relation was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_reflexiveClosure_relationExistsWithNoop() {
        // test [[(x,y) \in *NOOP(f)]] := ReflexiveClosure(f(x,y)) if f already exists
        // prime the relation by translating a field f
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field fieldF = sig.addField("f", sig); // f is of type S->S
        translator.translate(fieldF, context);

        // figure out what its relation was
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl funcF = context.getTheory().functionDeclarations().head();

        // test the actual translation
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)),
                        ExprUnary.Op.NOOP.make(null, fieldF).reflexiveClosure()), context);
        assertEquals(Term.mkReflexiveClosure(funcF.name(), x, y), result);

        // ensure no relation was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_transitiveClosure_createRelation() {
        // test [[(x,y) \in ^e]] := Closure(f(x,y)) where f: (univ, univ)->Bool is a new relation, with the defining
        // axiom "forall x,y: univ . f(x,y) <=> [[(x,y) \in e]]"
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e = sig.product(sig); // type: sig * sig
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.closure()), context);

        // ensure a relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_reflexiveClosure_createRelation() {
        // test [[(x,y) \in *e]] := ReflexiveClosure(f(x,y)) where f: (univ, univ)->Bool is a new relation, with the
        // defining axiom "forall x,y: univ . f(x,y) <=> [[(x,y) \in e]]"
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e = sig.product(sig); // type: sig * sig
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.reflexiveClosure()), context);

        // ensure a relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveClosure_fieldButNoRelation() {
        // test [[(x,y) \in ^f]] := Closure(g(x,y)) where g: (univ, univ)->Bool is a new relation, with the defining
        // axiom "forall x,y: univ . g(x,y) <=> [[(x,y) \in f]]", where f is a field without an associated relation
        // (e.g. it was optimized by the function optimization)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field f = sig.addField("f", sig); // f is of type sig->sig
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in f]] from the axiom
        Var flagInF = makeFlagConstant("inF");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), f))), any()))
                .thenReturn(flagInF);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), f.closure()), context);

        // ensure a relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInF))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_reflexiveClosure_fieldButNoRelation() {
        // test [[(x,y) \in *f]] := RClosure(g(x,y)) where g: (univ, univ)->Bool is a new relation, with the defining
        // axiom "forall x,y: univ . g(x,y) <=> [[(x,y) \in f]]", where f is a field without an associated relation
        // (e.g. it was optimized by the function optimization)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Sig.Field f = sig.addField("f", sig); // f is of type sig->sig
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in f]] from the axiom
        Var flagInF = makeFlagConstant("inF");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), f))), any()))
                .thenReturn(flagInF);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), f.reflexiveClosure()), context);

        // ensure a relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInF))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveClosure_intToInt() {
        // test [[(x,y) \in ^e]] := Closure(f(x,y)) where f: (Int,Int)->Bool is a new relation, with the defining
        // axiom "forall x,y: Int . f(x,y) <=> [[(x,y) \in e]]"
        Expr e = ExprConstant.makeNUMBER(2).product(ExprConstant.makeNUMBER(2));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(Sort.Int()), y.of(Sort.Int())), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(Sort.Int()), y.of(Sort.Int())), e.closure()), context);

        // ensure a relation of type (Int,Int) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(Sort.Int(), relation.argSorts().head());
        assertEquals(Sort.Int(), relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(Sort.Int()), y.of(Sort.Int())),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_reflexiveClosure_intToInt() {
        // test [[(x,y) \in ^e]] := ReflexiveClosure(f(x,y)) where f: (Int,Int)->Bool is a new relation, with the
        // defining axiom "forall x,y: Int . f(x,y) <=> [[(x,y) \in e]]"
        Expr e = ExprConstant.makeNUMBER(2).product(ExprConstant.makeNUMBER(2));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(Sort.Int()), y.of(Sort.Int())), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x.of(Sort.Int()), y.of(Sort.Int())), e.reflexiveClosure()), context);

        // ensure a relation of type (Int,Int) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(Sort.Int(), relation.argSorts().head());
        assertEquals(Sort.Int(), relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(Sort.Int()), y.of(Sort.Int())),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveClosure_rejectsMixedUnivInt() {
        // test that translating [[(x,y) \in ^e]] fails when e is of type univ->Int, because that doesn't make sense
        Sig sig = new Sig.PrimSig("S");
        Expr e = sig.product(ExprConstant.makeNUMBER(2));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        assertThrows("Should fail because e: univ->Int and we don't support closure over mixing univ/Int",
                ErrorFatal.class,
                () -> translator.translate(
                        ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(Sort.Int())), e.closure()), context));
    }

    @Test
    public void testTranslate_reflexiveClosure_rejectsMixedUnivInt() {
        // test that translating [[(x,y) \in *e]] fails when e is of type univ->Int, because we don't support mixing
        // Int and other sorts
        Sig sig = new Sig.PrimSig("S");
        Expr e = sig.product(ExprConstant.makeNUMBER(2));
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        assertThrows("Should fail because e: univ->Int and we don't support closure over mixing univ/Int",
                ErrorFatal.class,
                () -> translator.translate(ExprElementOf.make(
                        TermTuple.fromVars(x.of(univ), y.of(Sort.Int())), e.reflexiveClosure()), context));
    }

    @Test
    public void testTranslate_transitiveClosure_translateTwice_onlyOneAuxRelation() {
        // test that when we translate [[(x,y) \in ^(e1+e2)]] twice, only one auxiliary relation is created
        // note: we use e1+e2 as they're nontrivially equivalent (i.e. isSame but not ==)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e1 = sig.product(sig);
        Sig.PrimSig sig2 = new Sig.PrimSig("s");
        Expr e2 = sig2.product(sig2);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e1+e2]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2)))), any()))
                .thenReturn(flagInE);

        // translate twice, using the copy the second time
        translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).closure()), context);
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).closure()), context);

        // ensure only one relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result of the 2nd translation correctly uses that relation
        assertEquals(Term.mkClosure(relation.name(), x, y), result);

        // ensure it has the correct axiom (still)
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_reflexiveClosure_translateTwice_onlyOneAuxRelation() {
        // test that when we translate [[(x,y) \in *(e1+e2)]] twice, only one auxiliary relation is created
        // note: we use e1+e2 as they're nontrivially equivalent (i.e. isSame but not ==)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e1 = sig.product(sig);
        Sig.PrimSig sig2 = new Sig.PrimSig("s");
        Expr e2 = sig2.product(sig2);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e1+e2]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2)))), any()))
                .thenReturn(flagInE);

        // translate twice, using the copy the second time
        translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).reflexiveClosure()), context);
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).reflexiveClosure()), context);

        // ensure only one relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result of the 2nd translation correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y), result);

        // ensure it has the correct axiom (still)
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveAndReflexiveClosure_translateTwice_onlyOneAuxRelation() {
        // test that translating [[(x,y) \in ^(e1+e2)]] then [[(x,y) \in *(e1+e2)]] only creates one aux relation
        // note: we use e1+e2 as they're nontrivially equivalent (i.e. isSame but not ==)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        Expr e1 = sig.product(sig);
        Sig.PrimSig sig2 = new Sig.PrimSig("s");
        Expr e2 = sig2.product(sig2);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");

        // mock out [[(x,y) \in e1+e2]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2)))), any()))
                .thenReturn(flagInE);

        // translate twice, using the copy the second time
        translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).closure()), context);
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e1.plus(e2).reflexiveClosure()), context);

        // ensure only one relation of type (univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(2, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result of the 2nd translation correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y), result);

        // ensure it has the correct axiom (still)
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveClosure_freeVariables() {
        // test [[(x,y) \in ^(v->v)]] := Closure(f(x,y,v)) where f: (univ, univ, univ)->Bool is a new relation, with the
        // defining axiom "forall x,y,v: univ . f(x,y) <=> [[(x,y) \in v->v]]"
        // this tests adding in auxiliary variables on closed-over functions to preserve context
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar v = makeTestVarWithType("v", Type.make(sig));
        Expr e = v.product(v);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Var vVar = Term.mkVar("v");
        context.addTermMapping("v", new AnnotatedTerm(vVar.of(univ)));

        // mock out [[(x,y) \in v->v]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.closure()), context);

        // ensure a relation of type (univ, univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(3, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().tail().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkClosure(relation.name(), x, y, Collections.singletonList(vVar)), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ), vVar.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y, vVar),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_reflexiveClosure_freeVariables() {
        // test [[(x,y) \in *(v->v)]] := ReflexiveClosure(f(x,y,v)) where f: (univ, univ, univ)->Bool is a new relation,
        // with the defining axiom "forall x,y,v: univ . f(x,y) <=> [[(x,y) \in v->v]]"
        // this tests adding in auxiliary variables on closed-over functions to preserve context
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar v = makeTestVarWithType("v", Type.make(sig));
        Expr e = v.product(v);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Var vVar = Term.mkVar("v");
        context.addTermMapping("v", new AnnotatedTerm(vVar.of(univ)));

        // mock out [[(x,y) \in v->v]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.reflexiveClosure()), context);

        // ensure a relation of type (univ, univ, univ) -> Bool was added
        assertEquals(1, context.getTheory().functionDeclarations().size());
        FuncDecl relation = context.getTheory().functionDeclarations().head();
        assertEquals(3, relation.arity());
        assertEquals(univ, relation.argSorts().head());
        assertEquals(univ, relation.argSorts().tail().head());
        assertEquals(univ, relation.argSorts().last());
        assertEquals(Sort.Bool(), relation.resultSort());

        // ensure the result correctly uses that relation
        assertEquals(Term.mkReflexiveClosure(relation.name(), x, y, Collections.singletonList(vVar)), result);

        // ensure the correct axiom was added
        assertEquals(1, context.getTheory().axioms().size());
        Term axiom = context.getTheory().axioms().head();
        assertThat(axiom, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ), vVar.of(univ)),
                        Term.mkIff(
                                Term.mkApp(relation.name(), x, y, vVar),
                                flagInE))));
        // make *extra* sure that it used the correct relation name
        Forall forall = (Forall) axiom;
        Iff innerIff = (Iff) forall.body();
        App relationApp = (App) innerIff.left();
        assertEquals(relation.name(), relationApp.functionName());
    }

    @Test
    public void testTranslate_transitiveClosure_freeVariablesGeneratesDifferentAuxFunction() {
        // test that closing over the same function with different numbers of free variables generates
        // different auxiliary functions
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar v = makeTestVarWithType("v", Type.make(sig));
        Expr e = v.product(v);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Var vVar = Term.mkVar("v");

        // mock out [[(x,y) \in v->v]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        // with one free variable
        context.addTermMapping("v", new AnnotatedTerm(vVar.of(univ)));
        Term result1 = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.closure()), context);

        // with no free variables - "v" is mapped to univ
        context.removeMapping("v");
        context.addLetMapping("v", Sig.UNIV);
        delegateToRealTranslator(); // easier than mocking out the univ->univ translation
        Term result2 = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.closure()), context);

        // assert that two different functions were generated: univ^3 -> Bool and univ^2 -> Bool
        assertEquals(2, context.getTheory().functionDeclarations().size());

        FuncDecl oneFreeVarRel = context.getTheory().functionDeclarations().head();
        assertEquals(3, oneFreeVarRel.arity());
        assertEquals(univ, oneFreeVarRel.argSorts().head());
        assertEquals(univ, oneFreeVarRel.argSorts().tail().head());
        assertEquals(univ, oneFreeVarRel.argSorts().last());
        assertEquals(Sort.Bool(), oneFreeVarRel.resultSort());

        FuncDecl noFreeVarsRel = context.getTheory().functionDeclarations().last();
        assertEquals(2, noFreeVarsRel.arity());
        assertEquals(univ, noFreeVarsRel.argSorts().head());
        assertEquals(univ, noFreeVarsRel.argSorts().last());
        assertEquals(Sort.Bool(), noFreeVarsRel.resultSort());

        // ensure the results are correct
        assertEquals(Term.mkClosure(oneFreeVarRel.name(), x, y, Collections.singletonList(vVar)), result1);
        assertEquals(Term.mkClosure(noFreeVarsRel.name(), x, y), result2);

        // ensure the correct axioms were added
        assertEquals(2, context.getTheory().axioms().size());
        Term axiom1 = context.getTheory().axioms().head();
        Term axiom2 = context.getTheory().axioms().last();
        assertThat(axiom1, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ), vVar.of(univ)),
                        Term.mkIff(
                                Term.mkApp(oneFreeVarRel.name(), x, y, vVar),
                                flagInE))));
        assertThat(axiom2, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(noFreeVarsRel.name(), x, y),
                                Term.mkAnd(Term.mkTop(), Term.mkTop()))))); // [[(x,y) \in univ->univ]]
    }

    @Test
    public void testTranslate_reflexiveClosure_freeVariablesGeneratesDifferentAuxFunction() {
        // test that closing over the same function with different numbers of free variables generates
        // different auxiliary functions
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar v = makeTestVarWithType("v", Type.make(sig));
        Expr e = v.product(v);
        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Var vVar = Term.mkVar("v");

        // mock out [[(x,y) \in v->v]] from the axiom
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e))), any()))
                .thenReturn(flagInE);

        // with one free variable
        context.addTermMapping("v", new AnnotatedTerm(vVar.of(univ)));
        Term result1 = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.reflexiveClosure()), context);

        // with no free variables - "v" is mapped to univ
        context.removeMapping("v");
        context.addLetMapping("v", Sig.UNIV);
        delegateToRealTranslator(); // easier than mocking out the univ->univ translation
        Term result2 = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x.of(univ), y.of(univ)), e.reflexiveClosure()), context);

        // assert that two different functions were generated: univ^3 -> Bool and univ^2 -> Bool
        assertEquals(2, context.getTheory().functionDeclarations().size());

        FuncDecl oneFreeVarRel = context.getTheory().functionDeclarations().head();
        assertEquals(3, oneFreeVarRel.arity());
        assertEquals(univ, oneFreeVarRel.argSorts().head());
        assertEquals(univ, oneFreeVarRel.argSorts().tail().head());
        assertEquals(univ, oneFreeVarRel.argSorts().last());
        assertEquals(Sort.Bool(), oneFreeVarRel.resultSort());

        FuncDecl noFreeVarsRel = context.getTheory().functionDeclarations().last();
        assertEquals(2, noFreeVarsRel.arity());
        assertEquals(univ, noFreeVarsRel.argSorts().head());
        assertEquals(univ, noFreeVarsRel.argSorts().last());
        assertEquals(Sort.Bool(), noFreeVarsRel.resultSort());

        // ensure the results are correct
        assertEquals(Term.mkReflexiveClosure(oneFreeVarRel.name(), x, y, Collections.singletonList(vVar)), result1);
        assertEquals(Term.mkReflexiveClosure(noFreeVarsRel.name(), x, y), result2);

        // ensure the correct axioms were added
        assertEquals(2, context.getTheory().axioms().size());
        Term axiom1 = context.getTheory().axioms().head();
        Term axiom2 = context.getTheory().axioms().last();
        assertThat(axiom1, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ), vVar.of(univ)),
                        Term.mkIff(
                                Term.mkApp(oneFreeVarRel.name(), x, y, vVar),
                                flagInE))));
        assertThat(axiom2, isAlphaEquivalentTerm(
                Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)),
                        Term.mkIff(
                                Term.mkApp(noFreeVarsRel.name(), x, y),
                                Term.mkAnd(Term.mkTop(), Term.mkTop()))))); // [[(x,y) \in univ->univ]]
    }

    @Test
    public void testTranslate_transitiveClosure_letsAreDisambiguated() {
        // Test that two different auxiliary functions are generated in the following:
        //   sig A { a: set A, b: set A }
        //   pred f[x: A->A] { no ^x }
        //   run { f[a] and f[b] } // both should get different auxiliary functions
        delegateToRealTranslator();
        Sig.PrimSig sig = new Sig.PrimSig("S");
        when(mockScoper.sig2scope(sig)).thenReturn(2);
        when(mockScoper.isExact(sig)).thenReturn(false);
        Sig.Field a = sig.addField("a", sig.setOf());
        Sig.Field b = sig.addField("b", sig.setOf());
        ExprVar x = ExprVar.make(null, "x", Type.make(sig).product(Type.make(sig)));
        Decl xDecl = new Decl(null, null, null, null, Collections.singletonList(x), sig.product(sig));
        Expr fBody = x.closure().no();
        Func f = new Func(null, null, "f", Collections.singletonList(xDecl), null, fBody);
        Expr runBody = ExprCall.make(null, null, f, Collections.singletonList(a), 0)
                .and(ExprCall.make(null, null, f, Collections.singletonList(b), 0));

        // Translate the sig, fields, and the run statement, just make sure they don't return null
        assertNotNull(translator.translate(sig, context));
        assertNotNull(translator.translate(a, context));
        assertNotNull(translator.translate(b, context));
        assertNotNull(translator.translate(runBody, context));

        // We should have five predicates: inA, two for a and b, and two auxiliary functions
        assertEquals(5, context.getTheory().functionDeclarations().size());
    }

    @Test
    public void testTranslate_all_oneVar() {
        // test [[all x: e | f]] := forall x: univ . [[x \in e]] => [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e))), any()))
                .thenReturn(flagInE);

        AtomicReference<AnnotatedVar> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x"));
            AnnotatedTerm term = context.getTermMapping("x");
            assertNotNull(term);
            assertTrue(term.getTerm() instanceof Var);
            fortressX.set(new AnnotatedVar((Var) term.getTerm(), term.getSort()));
            return flagSub;
        });

        Term result = translator.translate(f.forAll(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(fortressX.get(), Term.mkImp(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasTermMapping("x"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_all_twoVars() {
        // test [[all x1: e1, x2: e2 | f]] := forall x1, x2: univ . [[x1 \in e1]] && [[x2 \in e2]] => [[f]]
        Sig.PrimSig sig1 = new Sig.PrimSig("S1"), sig2 = new Sig.PrimSig("S2");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig1));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig2));
        Decl x1 = e1.oneOf("x1"), x2 = e2.oneOf("x2");
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE1 = makeFlagConstant("x1InE1"), flagInE2 = makeFlagConstant("x2InE2");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e1))), any()))
                .thenReturn(flagInE1, flagInE2);

        AtomicReference<AnnotatedVar> fortressX1 = new AtomicReference<>();
        AtomicReference<AnnotatedVar> fortressX2 = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure x1 and x2 have mappings here and capture them
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x1"));
            assertTrue(context.hasTermMapping("x2"));
            AnnotatedTerm term1 = context.getTermMapping("x1");
            assertNotNull(term1);
            assertTrue(term1.getTerm() instanceof Var);
            fortressX1.set(new AnnotatedVar((Var) term1.getTerm(), term1.getSort()));
            AnnotatedTerm term2 = context.getTermMapping("x2");
            assertNotNull(term2);
            assertTrue(term2.getTerm() instanceof Var);
            fortressX2.set(new AnnotatedVar((Var) term2.getTerm(), term2.getSort()));
            return flagSub;
        });

        Term result = translator.translate(f.forAll(x1, x2), context);
        assertNotNull(fortressX1.get()); // make sure we captured references, so we translated [[f]]
        assertNotNull(fortressX2.get());
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(
                Arrays.asList(fortressX1.get(), fortressX2.get()),
                Term.mkImp(Term.mkAnd(flagInE1, flagInE2), flagSub));
        assertEquals(expected, result);

        // make sure the mappings were removed after translation
        assertFalse(context.hasTermMapping("x1"));
        assertFalse(context.hasTermMapping("x2"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_all_noMultiplicity() {
        // test [[all x: e | f]] := forall x: univ . [[x \in e]] => [[f]], even when we don't wrap e with ONEOF
        // (the Alloy Analyzer occasionally generates these, like in `run somePredicate` commands)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        ExprVar xVar = makeTestVarWithType("x", e.type());
        Decl x = new Decl(null, null, null, null, ConstList.make(Collections.singletonList(xVar)), e);
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e))), any()))
                .thenReturn(flagInE);

        AtomicReference<AnnotatedVar> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x"));
            AnnotatedTerm term = context.getTermMapping("x");
            assertNotNull(term);
            assertTrue(term.getTerm() instanceof Var);
            fortressX.set(new AnnotatedVar((Var) term.getTerm(), term.getSort()));
            return flagSub;
        });

        Term result = translator.translate(f.forAll(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(fortressX.get(), Term.mkImp(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasTermMapping("x"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_all_disj() {
        // test [[all disj x1, x2: e | f]] := forall x1, x2: univ . [[x1 \in e]] && [[x2 \in e]] =>
        //   [[disj[x1,x2]]] => [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S1");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        ExprVar x1 = makeTestFormulaVar("x1"), x2 = makeTestFormulaVar("x2");
        Decl xs = new Decl(null, new Pos(null, 0, 0), null, null, Arrays.asList(x1, x2), e); // make disjoint
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE1 = makeFlagConstant("x1InE1"), flagInE2 = makeFlagConstant("x2InE2");
        Var flagSub = makeFlagConstant("disjImpliesF");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e))), any()))
                .thenReturn(flagInE1, flagInE2);

        AtomicReference<AnnotatedVar> fortressX1 = new AtomicReference<>();
        AtomicReference<AnnotatedVar> fortressX2 = new AtomicReference<>();
        when(mockRoot.translate(
                argThat(isAlphaEquivalent(ExprList.makeDISJOINT(null, null, Arrays.asList(x1, x2)).implies(f))), any()))
                .then(ctx -> {
                    // make sure x1 and x2 have mappings here and capture them
                    TranslationContext context = ctx.getArgument(1);
                    assertTrue(context.hasTermMapping("x1"));
                    assertTrue(context.hasTermMapping("x2"));
                    AnnotatedTerm term1 = context.getTermMapping("x1");
                    assertNotNull(term1);
                    assertTrue(term1.getTerm() instanceof Var);
                    fortressX1.set(new AnnotatedVar((Var) term1.getTerm(), term1.getSort()));
                    AnnotatedTerm term2 = context.getTermMapping("x2");
                    assertNotNull(term2);
                    assertTrue(term2.getTerm() instanceof Var);
                    fortressX2.set(new AnnotatedVar((Var) term2.getTerm(), term2.getSort()));
                    return flagSub;
                });

        Term result = translator.translate(f.forAll(xs), context);
        assertNotNull(fortressX1.get()); // make sure we captured references, so we translated [[f]]
        assertNotNull(fortressX2.get());
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(
                Arrays.asList(fortressX1.get(), fortressX2.get()),
                Term.mkImp(Term.mkAnd(flagInE1, flagInE2), flagSub));
        assertEquals(expected, result);

        // make sure the mappings were removed after translation
        assertFalse(context.hasTermMapping("x1"));
        assertFalse(context.hasTermMapping("x2"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_some() {
        // test [[some x: e | f]] := exists x: univ . [[x \in e]] && [[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        // "e" gets translated to "one e" at some point
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e))), any()))
                .thenReturn(flagInE);

        AtomicReference<AnnotatedVar> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x"));
            AnnotatedTerm term = context.getTermMapping("x");
            assertNotNull(term);
            assertTrue(term.getTerm() instanceof Var);
            fortressX.set(new AnnotatedVar((Var) term.getTerm(), term.getSort()));
            return flagSub;
        });

        Term result = translator.translate(f.forSome(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkExists(fortressX.get(), Term.mkAnd(flagInE, flagSub));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasTermMapping("x"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_no() {
        // test [[no x: e | f]] := forall x: univ | [[x \in e]] => ![[f]]
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl x = e.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");
        Var flagInE = makeFlagConstant("xInE");
        Var flagSub = makeFlagConstant("f");
        Var flagX = makeFlagConstant("x");

        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(flagX.of(univ), e))), any()))
                .thenReturn(flagInE);

        AtomicReference<AnnotatedVar> fortressX = new AtomicReference<>();
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            // make sure that x |-> fortressX appears in the context map when translating [[f]],
            // and capture the fortressX constant to construct the expected translation later
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x"));
            AnnotatedTerm term = context.getTermMapping("x");
            assertNotNull(term);
            assertTrue(term.getTerm() instanceof Var);
            fortressX.set(new AnnotatedVar((Var) term.getTerm(), term.getSort()));
            return flagSub;
        });

        Term result = translator.translate(f.forNo(x), context);
        assertNotNull(fortressX.get()); // make sure we captured a reference, so we translated [[f]]
        // use the captured reference to construct the expected translation
        Term expected = Term.mkForall(fortressX.get(), Term.mkImp(flagInE, Term.mkNot(flagSub)));
        assertEquals(expected, result);

        // make sure the x |-> fortressX mapping was removed after translating [[f]]
        assertFalse(context.hasTermMapping("x"));
        assertContextEmpty();
    }

    @Test
    public void testTranslate_lone() {
        // test [[lone x: e | f]] := forall x, y: univ . [[x \in e]] && [[y \in e]] && [[f]] && [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", univ, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", univ, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x").of(univ), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term expected = Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)), Term.mkImp(
                Term.mkAnd(
                        Term.mkApp("inE", x),
                        Term.mkApp("inE", y),
                        Term.mkApp("f", x),
                        Term.mkApp("f", y)),
                Term.mkEq(x, y)));

        Term result = translator.translate(f.forLone(alloyX), context);
        assertThat(result, isAlphaEquivalentTerm(expected));

        // make sure the x |-> fortressX mapping was removed
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_one() {
        // test [[one x: e | f]] := exists x: univ . [[x \in e]] && [[f]] && forall y: S . [[y \in e]] &&
        //   [[f[y/x]]] => x = y
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");

        // use flag predicates for [[\in e]] and [[f]] to make sure the substitution happens correctly
        FuncDecl flagInE = FuncDecl.mkFuncDecl("inE", univ, Sort.Bool());
        FuncDecl flagF = FuncDecl.mkFuncDecl("f", univ, Sort.Bool());
        context.addFunctionDeclaration(flagInE);
        context.addFunctionDeclaration(flagF);

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x").of(univ), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        Var x = Term.mkVar("x"), y = Term.mkVar("y");
        Term expected = Term.mkExists(x.of(univ), Term.mkAnd(
                Term.mkApp("inE", x),
                Term.mkApp("f", x),
                Term.mkForall(y.of(univ), Term.mkImp(
                        Term.mkAnd(
                                Term.mkApp("inE", y),
                                Term.mkApp("f", y)),
                        Term.mkEq(x, y)))));

        Term result = translator.translate(f.forOne(alloyX), context);
        assertThat(result, isAlphaEquivalentTerm(expected));

        // make sure the x mapping was removed
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_sum_oneVar_scope1() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1]
        // where univ has scope 1 and @n is the nth domain element in univ
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x").of(univ), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        DomainElement domElem = DomainElement.apply(1, univ);
        Term expected = Term.mkIfThenElse(
                Term.mkApp("inE", domElem),
                Term.mkApp("f", domElem),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX), context);
        assertEquals(expected, result);

        // make sure the x mapping was removed
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_sum_oneVar_scope2() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1] + ([[x \in e]] => [[f]] else 0)[x/@2]
        // where univ has scope 2 and @n is the nth domain element in univ
        doReturn(2).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x").of(univ), e))), any()))
                .then(useTestFunction("inE", "x"));

        // translate [[f]] with a function f(x)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x"));

        DomainElement domElem1 = DomainElement.apply(1, univ);
        DomainElement domElem2 = DomainElement.apply(2, univ);
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
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_sum_twoVars_scope1() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@1]
        // where univ has scope 1 and @n is the nth domain element in univ
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0").of(univ), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0").of(univ), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElem = DomainElement.apply(1, univ);
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(
                        Term.mkApp("inE1", domElem),
                        Term.mkApp("inE2", domElem)),
                Term.mkApp("f", domElem, domElem),
                IntegerLiteral.apply(0));
        Term result = translator.translate(f.sumOver(alloyX, alloyY), context);
        assertEquals(expected, result);

        // make sure the mappings were removed
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));
    }

    @Test
    public void testTranslate_sum_twoVars_scope2() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@1]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1,y/@2]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@2,y/@1]
        //   + (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@2,y/@2]
        // nesting left-to-right, where univ has scope 2 and @n is the nth domain element in univ
        doReturn(2).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestVarWithType("e2", Type.make(sig));
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0").of(univ), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0").of(univ), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElem1 = DomainElement.apply(1, univ);
        DomainElement domElem2 = DomainElement.apply(2, univ);
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
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));
    }

    @Test
    public void testTranslate_sum_oneVar_int() {
        // test [[sum x: e | f]] := ([[x \in e]] => [[f]] else 0)[x/@1]
        // where the bitwidth is 0 and @n is the nth domain element in Int, and e is of type Int
        when(mockScoper.getBitwidth()).thenReturn(0);
        ExprVar e = makeTestSmallIntVar("e");
        Decl alloyX = e.oneOf("x");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x").of(Sort.Int()), e))), any()))
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
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_sum_mixedIntNonInt() {
        // test [[sum x: e1, y: e2 | f]] := (([[x \in e1]] && [[y \in e2]]) => [[f]] else 0)[x/@1u,y/@1i]
        // where univ has scope 1, bitwidth is 0, @1u is the 1st univ domain element, @1i is the 1st Int domain element,
        // e1 is in univ and e2 is in Int
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e1 = makeTestVarWithType("e1", Type.make(sig));
        ExprVar e2 = makeTestSigIntVar("e2");
        Decl alloyX = e1.oneOf("x");
        Decl alloyY = e2.oneOf("y");
        ExprVar f = makeTestSmallIntVar("f");

        // translate [[x \in e1]] with a function inE1(x) and similar for [[y \in e2]] and inE2(y)
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("x_0").of(univ), e1))), any()))
                .then(useTestFunction("inE1", "x"));
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(Term.mkVar("y_0").of(Sort.Int()), e2))), any()))
                .then(useTestFunction("inE2", "y"));

        // translate [[f]] with a function f(x,y)
        when(mockRoot.translate(eq(f), any())).then(useTestFunction("f", "x", "y"));

        DomainElement domElemUniv = DomainElement.apply(1, univ);
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
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("y"));
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

        Term result = translator.translate(ExprElementOf.make(x.of(Sort.Int()), sum), context);
        assertEquals(Term.mkEq(x, flagSum), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_unary_scope1() {
        // test [[#e]] := ([[x0 \in e]] => 1 else 0)[x0/@1]
        // where e is unary, univ has scope 1, and @n is the nth domain element in univ
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x0").of(univ), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.getTerm(0));
                });

        DomainElement domElem = DomainElement.apply(1, univ);
        Term expected = Term.mkIfThenElse(Term.mkApp("inE", domElem), IntegerLiteral.apply(1), IntegerLiteral.apply(0));
        Term result = translator.translate(e.cardinality(), context);
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_cardinality_binary_scope1() {
        // test [[#e]] := ([[(x0,x1) \in e]] => 1 else 0)[x0/@1,x1/@1]
        // where e is binary, univ has scope 1, and @n is the nth domain element in univ
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(
                        Term.mkVar("x0").of(univ), Term.mkVar("x1").of(univ)), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.getTerm(0), translated.tuple.getTerm(1));
                });

        DomainElement domElem = DomainElement.apply(1, univ);
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
        doReturn(1).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(Sig.SIGINT)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(
                        TermTuple.fromVars(Term.mkVar("x0").of(univ), Term.mkVar("x1").of(Sort.Int())), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.getTerm(0), translated.tuple.getTerm(1));
                });

        DomainElement domElemUniv = DomainElement.apply(1, univ);
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
        doReturn(2).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(Term.mkVar("x0").of(univ), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.getTerm(0));
                });

        DomainElement domElem1 = DomainElement.apply(1, univ);
        DomainElement domElem2 = DomainElement.apply(2, univ);
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
        doReturn(2).when(mockSortPolicy).getSortScope(eq(univ));
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));

        // translate [[x0 \in e]] with a function inE(x)
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(TermTuple.fromVars(
                        Term.mkVar("x0").of(univ), Term.mkVar("x1").of(univ)), e))), any()))
                .then(ctx -> {
                    ExprElementOf translated = ctx.getArgument(0);
                    return Term.mkApp("inE", translated.tuple.getTerm(0), translated.tuple.getTerm(1));
                });

        DomainElement domElem1 = DomainElement.apply(1, univ);
        DomainElement domElem2 = DomainElement.apply(2, univ);
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
        ExprVar f = makeTestFormulaVar("f");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagInE);

        // mock out [[f]] where y is mapped to x
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("y"));
            assertEquals(x, Objects.requireNonNull(context.getTermMapping("y")).getTerm());
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(x.of(univ), f.comprehensionOver(y));
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
        ExprVar f = makeTestFormulaVar("f");

        // mock out [[x1 \in e1]] and [[x2 \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x1.of(univ), e1))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x2.of(univ), e2))), any()))
                .thenReturn(flagInE2);

        // mock out [[f]] where y1 is mapped to x1, y2 is mapped to x2
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("y1"));
            assertTrue(context.hasTermMapping("y2"));
            assertEquals(x1, Objects.requireNonNull(context.getTermMapping("y1")).getTerm());
            assertEquals(x2, Objects.requireNonNull(context.getTermMapping("y2")).getTerm());
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(
                TermTuple.fromVars(x1.of(univ), x2.of(univ)), f.comprehensionOver(y1, y2));
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
        ExprVar f = makeTestFormulaVar("f");

        // mock out [[x1 \in e1]] and [[x2 \in e2]]
        Var flagInE1 = makeFlagConstant("inE1"), flagInE2 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x1.of(univ), e))), any()))
                .thenReturn(flagInE1);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x2.of(univ), e))), any()))
                .thenReturn(flagInE2);

        // mock out [[f]] where y1 is mapped to x1, y2 is mapped to x2
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("y1"));
            assertTrue(context.hasTermMapping("y2"));
            assertEquals(x1, Objects.requireNonNull(context.getTermMapping("y1")).getTerm());
            assertEquals(x2, Objects.requireNonNull(context.getTermMapping("y2")).getTerm());
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), f.comprehensionOver(ys));
        Term result = translator.translate(comprehension, context);
        assertEquals(Term.mkAnd(flagInE1, flagInE2, flagMappedF), result);
        assertContextEmpty(); // should clear context
    }

    @Test
    public void testTranslate_comprehension_varRefInBound() {
        // test [[(x1, x2) \in {y1: e, y2: y1 | f}]] := [[x1 \in e]] && [[x2 \in y1]] && [[f]]
        // where y1 is mapped to x1 (during [[x2 \in y1]]) and y2 is mapped to x2
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        ExprVar e = makeTestVariable("e");
        Decl y1 = e.oneOf("y1");
        Decl y2 = y1.get().oneOf("y2");
        ExprVar f = makeTestFormulaVar("f");

        // mock out [[x1 \in e]] and [[x2 \in y1]], where in the latter y1 is mapped to x1
        Var flagInE = makeFlagConstant("inE"), flagInY1 = makeFlagConstant("inE2");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x1.of(univ), e))), any()))
                .thenReturn(flagInE);
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x2.of(univ), y1.get()))), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("y1"));
            assertFalse(context.hasTermMapping("y2")); // no y2 yet, we're too early
            assertEquals(x1, Objects.requireNonNull(context.getTermMapping("y1")).getTerm());
            return flagInY1;
        });

        // mock out [[f]] where y1 is mapped to x1, y2 is mapped to x2
        Var flagMappedF = makeFlagConstant("mappedF");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("y1"));
            assertTrue(context.hasTermMapping("y2"));
            assertEquals(x1, Objects.requireNonNull(context.getTermMapping("y1")).getTerm());
            assertEquals(x2, Objects.requireNonNull(context.getTermMapping("y2")).getTerm());
            return flagMappedF;
        });

        Expr comprehension = ExprElementOf.make(
                TermTuple.fromVars(x1.of(univ), x2.of(univ)), f.comprehensionOver(y1, y2));
        Term result = translator.translate(comprehension, context);
        assertEquals(Term.mkAnd(flagInE, flagInY1, flagMappedF), result);
        assertContextEmpty(); // should clear context
    }

    @Test
    public void testTranslate_someExpr() {
        // test [[some e]] := exists x: univ | [[x \in e]] && true
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Var x = Term.mkVar("x0_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.some(), context);
        assertEquals(Term.mkExists(x.of(univ), Term.mkAnd(flagInE, Term.mkTop())), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_someExpr_binary() {
        // test [[some e]] := exists x0, x1: univ | [[(x0,x1) \in e]] && true, where arity(e) = 2
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(sig)));
        Var x0 = Term.mkVar("x0_0");
        Var x1 = Term.mkVar("x1_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x0.of(univ), x1.of(univ)), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.some(), context);
        Term expected = Term.mkExists(Arrays.asList(x0.of(univ), x1.of(univ)),
                Term.mkAnd(flagInE, Term.mkTop()));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_someExpr_int() {
        // test [[some e]] := exists x: Int | [[x \in e]] && true, where e is of type Int
        ExprVar e = makeTestSigIntVar("e");
        Var x = Term.mkVar("x0_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(Sort.Int()), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.some(), context);
        assertEquals(Term.mkExists(x.of(Sort.Int()), Term.mkAnd(flagInE, Term.mkTop())), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_someExpr_binaryMixedIntNonInt() {
        // test [[some e]] := exists x0: univ, x1: Int | [[(x0,x1) \in e]] && true, where e is of type S->Int
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig).product(Type.make(Sig.SIGINT)));
        Var x0 = Term.mkVar("x0_0");
        Var x1 = Term.mkVar("x1_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(
                ExprElementOf.make(TermTuple.fromVars(x0.of(univ), x1.of(Sort.Int())), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.some(), context);
        Term expected = Term.mkExists(Arrays.asList(x0.of(univ), x1.of(Sort.Int())),
                Term.mkAnd(flagInE, Term.mkTop()));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_noExpr() {
        // test [[no e]] := forall x: univ | [[x \in e]] => !true
        // (a bit convoluted, but that's okay since it makes Portus simpler)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Var x = Term.mkVar("x0_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.no(), context);
        assertEquals(Term.mkForall(x.of(univ), Term.mkImp(flagInE, Term.mkNot(Term.mkTop()))), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_loneExpr() {
        // test [[lone e]] := forall x,y: univ | [[x \in e]] && [[y \in e]] && true && true => x = y
        // (a bit convoluted, but that's okay since it makes Portus simpler)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Var x = Term.mkVar("x0_0");
        Var y = Term.mkVar("x0_0_prime_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.lone(), context);
        Term expected = Term.mkForall(Arrays.asList(x.of(univ), y.of(univ)), Term.mkImp(
                Term.mkAnd(flagInE, flagInE, Term.mkTop(), Term.mkTop()),
                Term.mkEq(x, y)));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_oneExpr() {
        // test [[one e]] := exists x: univ | [[x \in e]] && true && forall y: univ . [[y \in e]] && true => x = y
        // (a bit convoluted, but that's okay since it makes Portus simpler)
        Sig.PrimSig sig = new Sig.PrimSig("S");
        ExprVar e = makeTestVarWithType("e", Type.make(sig));
        Var x = Term.mkVar("x0_0");
        Var y = Term.mkVar("x0_0_prime_0");

        // mock out [[x \in e]]
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any())).thenReturn(flagInE);

        Term result = translator.translate(e.one(), context);
        Term expected = Term.mkExists(x.of(univ), Term.mkAnd(flagInE, Term.mkTop(),
                Term.mkForall(y.of(univ), Term.mkImp(
                        Term.mkAnd(flagInE, Term.mkTop()),
                        Term.mkEq(x, y)))));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_disj() {
        // test [[disj[e1,e2]]] := DISTINCT(v1,v2) where e1,e2 are variables bound to v1,v2
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2");
        Var v1 = Term.mkVar("v1"), v2 = Term.mkVar("v2");
        context.addTermMapping("e1", new AnnotatedTerm(v1.of(univ)));
        context.addTermMapping("e2", new AnnotatedTerm(v2.of(univ)));
        Term result = translator.translate(ExprList.makeDISJOINT(null, null, Arrays.asList(e1, e2)), context);
        assertEquals(Term.mkDistinct(v1, v2), result);
    }

    @Test
    public void testTranslate_disj_3vars() {
        // test [[disj[e1,e2,e3]]] := DISTINCT(v1,v2,v3) where e1,e2,e3 are variables bound to v1,v2,v3
        ExprVar e1 = makeTestVariable("e1"), e2 = makeTestVariable("e2"), e3 = makeTestVariable("e3");
        Var v1 = Term.mkVar("v1"), v2 = Term.mkVar("v2"), v3 = Term.mkVar("v3");
        context.addTermMapping("e1", new AnnotatedTerm(v1.of(univ)));
        context.addTermMapping("e2", new AnnotatedTerm(v2.of(univ)));
        context.addTermMapping("e3", new AnnotatedTerm(v3.of(univ)));
        Term result = translator.translate(ExprList.makeDISJOINT(null, null, Arrays.asList(e1, e2, e3)), context);
        assertEquals(Term.mkDistinct(v1, v2, v3), result);
    }

    @Test
    public void testTranslate_let() {
        // test [[let x = e | f(x)]] := [[f(e)]]
        ExprVar e = makeTestVariable("e");
        ExprVar x = makeTestVariable("x");
        ExprVar f = makeTestFormulaVar("f");

        // make sure the argument is e and the context was saved
        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x"));
            TranslationContext.LetContext letContext = context.getLetMapping("x");
            assertNotNull(letContext);
            assertEquals(e, letContext.getExpr());

            // make sure we saved the correct context (should be empty)
            letContext.useLetMapping(context);
            assertContextEmpty(context);
            letContext.resetMapping();

            return flag;
        });

        Term result = translator.translate(ExprLet.make(null, x, e, f), context);
        assertEquals(flag, result);

        // make sure x is flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_let_recursion() {
        // test [[let x = x | f]] := [[f]] (and there's no infinite recursion)
        ExprVar x = makeTestVariable("x");
        ExprVar f = makeTestFormulaVar("f");

        delegateToRealTranslator();
        Var flagF = makeFlagConstant("flag");
        doReturn(flagF).when(mockRoot).translate(eq(f), any());

        Term result = translator.translate(ExprLet.make(null, x, x, f), context);
        assertEquals(flagF, result);
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_let_nested() {
        // test [[let a = e | let e = x | a]] := [[e]], not [[x]]
        // this tests that context is saved/restored correctly
        ExprVar a = makeTestFormulaVar("a");
        ExprVar e = makeTestVariable("e");
        ExprVar x = makeTestVariable("x");

        Var fortressE = Term.mkVar("e");
        context.addTermMapping("e", new AnnotatedTerm(fortressE.of(univ)));
        delegateToRealTranslator();

        Term result = translator.translate(ExprLet.make(null, a, e, ExprLet.make(null, e, x, a)), context);
        assertEquals(fortressE, result);

        // make sure things are flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("a"));
        assertFalse(context.hasTermMapping("a"));
        assertTrue(context.hasTermMapping("e"));
        assertEquals(fortressE, Objects.requireNonNull(context.getTermMapping("e")).getTerm());
    }

    @Test
    public void testTranslate_let_expr() {
        // test [[x0 \in let x = e | f(x)]] := [[x0 \in f(e)]]
        ExprVar e = makeTestVariable("e");
        ExprVar x = makeTestVariable("x");
        ExprVar f = makeTestFormulaVar("f");
        Var x0 = Term.mkVar("x0");

        // make sure the argument is e and the context was saved
        Var flag = makeFlagConstant("flag");
        when(mockRoot.translate(argThat(isAlphaEquivalent(ExprElementOf.make(x0.of(univ), f))), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("x"));
            TranslationContext.LetContext letContext = context.getLetMapping("x");
            assertNotNull(letContext);
            assertEquals(e, letContext.getExpr());

            // make sure we saved the correct context (should be empty)
            letContext.useLetMapping(context);
            assertContextEmpty(context);
            letContext.resetMapping();

            return flag;
        });

        Term result = translator.translate(ExprElementOf.make(x0.of(univ), ExprLet.make(null, x, e, f)), context);
        assertEquals(flag, result);

        // make sure x is flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasTermMapping("x"));
    }

    @Test
    public void testTranslate_variable_var() {
        // test [[x \in v]] := x = v for an Alloy variable v
        // explicitly set the variable mapping in the context
        ExprVar alloyVar = makeTestVariable("v");
        Var x = Term.mkVar("x");
        Var v = Term.mkVar("v");
        context.addTermMapping(alloyVar.label, new AnnotatedTerm(v.of(univ)));

        Term result = translator.translate(ExprElementOf.make(x.of(univ), alloyVar), context);
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
        TermTuple vars = TermTuple.fromVars(x1.of(univ), x2.of(univ));
        Var flagInE = makeFlagConstant("inE");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(vars, expr))), any()))
                .thenReturn(flagInE);

        Term result = translator.translate(ExprElementOf.make(vars, alloyVar), context);
        assertEquals(flagInE, result);
    }

    @Test
    public void testTranslate_pred_nilary() {
        // test [[ p[] ]] := [[f]] when "pred p { f }" is defined
        ExprVar f = makeTestFormulaVar("f");
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
        ExprVar f = makeTestFormulaVar("f");
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
        assertFalse(context.hasTermMapping("y"));
    }

    @Test
    public void testTranslate_pred_binary() {
        // test [[ b[y1, y2] ]] := [[f(y1, y2)]] when "pred b[x1: S, x2: S] { f(x1, x2) }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl x1Decl = sig.oneOf("x1");
        Decl x2Decl = sig.oneOf("x2");
        ExprVar y1 = makeTestVariable("y1");
        ExprVar y2 = makeTestVariable("y2");
        ExprVar f = makeTestFormulaVar("f");
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
        assertFalse(context.hasTermMapping("y1"));
        assertFalse(context.hasTermMapping("y2"));
    }

    @Test
    public void testTranslate_fun_nilary() {
        // test [[ x \in g[] ]] := [[x \in f]] when "fun g: S { f }" is defined
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        ExprVar f = makeTestVariable("f");
        Func fun = makeTestFunc("g", null, sig, f);
        Var x = Term.mkVar("x");
        TermTuple vars = TermTuple.fromVars(x.of(univ));

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
        TermTuple vars = TermTuple.fromVars(x.of(univ));

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
        assertFalse(context.hasTermMapping("y"));
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
        TermTuple vars = TermTuple.fromVars(x.of(univ));

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
        assertFalse(context.hasTermMapping("y1"));
        assertFalse(context.hasTermMapping("y2"));
    }

    @Test
    public void testTranslate_call_conflicting() {
        // An obscure case that came up in the Chord model:
        // "pred p[a: S, b: S] { f(a, b) }", [[ p[x, a] ]] := [[f(x, a)]] and not [[f(x, x)]], which is what could
        // happen if we naively translated p[x,a] as let a=x | let b=a | f(a,b)
        Sig.PrimSig sig = new Sig.PrimSig("Sig");
        Decl aDecl = sig.oneOf("a");
        Decl bDecl = sig.oneOf("b");
        ExprVar argX = makeTestVariable("x");
        ExprVar argA = makeTestVariable("a");
        ExprVar f = makeTestFormulaVar("f");
        Func pred = makeTestPred("p", Arrays.asList(aDecl, bDecl), f);

        // make sure the arguments are x, a
        Term flag = makeFlagConstant("flag");
        when(mockRoot.translate(eq(f), any())).then(ctx -> {
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasLetMapping("a"));
            assertTrue(context.hasLetMapping("b"));
            assertEquals(argX, Objects.requireNonNull(context.getLetMapping("a")).getExpr());
            assertEquals(argA, Objects.requireNonNull(context.getLetMapping("b")).getExpr());

            // Make sure a's let mapping doesn't further translate it (to x)
            TranslationContext.LetContext aLetMapping = Objects.requireNonNull(context.getLetMapping("b"));
            aLetMapping.useLetMapping(context);
            assertFalse(context.hasLetMapping("a"));
            assertFalse(context.hasLetMapping("b")); // for good measure
            aLetMapping.resetMapping();

            return flag;
        });

        Term result = translator.translate(pred.call(argX, argA), context);
        assertEquals(flag, result);

        // make sure x, a are flushed from the context's mapping
        assertContextEmpty();
        assertFalse(context.hasLetMapping("x"));
        assertFalse(context.hasLetMapping("a"));
        assertFalse(context.hasTermMapping("x"));
        assertFalse(context.hasTermMapping("a"));
    }

    @Test
    public void testTranslate_varAsExpression() {
        // test [[x]] := x (as an [integer] expression)
        Var x = Term.mkVar("x");
        context.addTermMapping("x", new AnnotatedTerm(x.of(univ)));
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
        Term result = translator.translate(ExprElementOf.make(x.of(Sort.Int()), ExprConstant.makeNUMBER(2)), context);
        assertEquals(Term.mkEq(x, IntegerLiteral.apply(2)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_quantifyOverInt() {
        // test [[all x: Int | f]] := forall x: Int . true => [[f]]
        // the 'true' is due to the [[x \in Int]] condition
        Decl x = Sig.SIGINT.oneOf("x");
        ExprVar f = makeTestFormulaVar("f");

        Term flagF = makeFlagConstant("flagF");
        AtomicReference<AnnotatedVar> fortressX = new AtomicReference<>();
        delegateToRealTranslator(); // for the [[x \in Int]] translation
        doAnswer(ctx -> {
            // make sure x has a mapping here and capture it
            TranslationContext context = ctx.getArgument(1);
            assertTrue(context.hasTermMapping("x"));
            AnnotatedTerm term = context.getTermMapping("x");
            assertNotNull(term);
            assertTrue(term.getTerm() instanceof Var);
            fortressX.set(new AnnotatedVar((Var) term.getTerm(), term.getSort()));
            return flagF;
        }).when(mockRoot).translate(eq(f), any());

        Term result = translator.translate(f.forAll(x), context);
        assertEquals(Term.mkForall(fortressX.get(), Term.mkImp(Term.mkTop(), flagF)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_inLiterals() {
        // unoptimized: test [[2 in 3]] := forall x: Int . [[x \in 2]] => [[x \in 3]]
        Var x = Term.mkVar("x0_0");

        Term flagIn2 = makeFlagConstant("in2"), flagIn3 = makeFlagConstant("in3");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(x.of(Sort.Int()), ExprConstant.makeNUMBER(2)))), any())).thenReturn(flagIn2);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(x.of(Sort.Int()), ExprConstant.makeNUMBER(3)))), any())).thenReturn(flagIn3);

        Term result = translator.translate(ExprConstant.makeNUMBER(2).in(ExprConstant.makeNUMBER(3)), context);
        assertEquals(Term.mkForall(x.of(Sort.Int()), Term.mkImp(flagIn2, flagIn3)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_int_eqLiterals() {
        // unoptimized: test [[2 = 3]] := forall x: Int . [[x \in 2]] <=> [[x \in 3]]
        Var x = Term.mkVar("x0_0");

        Term flagIn2 = makeFlagConstant("in2"), flagIn3 = makeFlagConstant("in3");
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(x.of(Sort.Int()), ExprConstant.makeNUMBER(2)))), any())).thenReturn(flagIn2);
        when(mockRoot.translate(argThat(isAlphaEquivalent(
                ExprElementOf.make(x.of(Sort.Int()), ExprConstant.makeNUMBER(3)))), any())).thenReturn(flagIn3);

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
    public void testTranslate_seq_inSeqIdx() {
        // test [[x \in seq/Int]] := x >= 0 && x <= maxseq-1, for maxseq = 5
        when(mockScoper.getMaxSeq()).thenReturn(5);
        when(mockScoper.getBitwidth()).thenReturn(4); // just need 2^(bitwidth-1) >= maxseq
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x.of(Sort.Int()), Sig.SEQIDX), context);
        Term expected = Term.mkAnd(
                Term.mkGE(x, IntegerLiteral.apply(0)),
                Term.mkLE(x, IntegerLiteral.apply(4)));
        assertEquals(expected, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_seq_inSeqIdx_false() {
        // test [[x \in seq/Int]] short circuits to bottom when x isn't an Int
        when(mockScoper.getMaxSeq()).thenReturn(5);
        when(mockScoper.getBitwidth()).thenReturn(4);
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x.of(Sort.Bool()), Sig.SEQIDX), context);
        assertEquals(Term.mkBottom(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_binaryOperationExpression_mixedIntNonInt_fails() {
        // test [[S X 2]] fails for select binary operations X, since we disallow mixing integers with non-integers
        Sig.PrimSig sig = new Sig.PrimSig("S");
        delegateToRealTranslator();
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
        delegateToRealTranslator();
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
            Expr mixedExpr = ExprElementOf.make(x.of(univ), op.make(null, null, sig, ExprConstant.makeNUMBER(2)));
            assertThrows("Should reject mixing integers with non-integers: " + op, ErrorFatal.class,
                    () -> translator.translate(mixedExpr, context));
        }
    }

    @Test
    public void testTranslate_univ() {
        // test [[x \in univ]] := true
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x.of(univ), Sig.UNIV), context);
        assertEquals(Term.mkTop(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_none() {
        // test [[x \in none]] := false
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x.of(univ), Sig.NONE), context);
        assertEquals(Term.mkBottom(), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_iden() {
        // test [[(x1, x2) \in iden] := x1 = x2
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");
        Term result = translator.translate(
                ExprElementOf.make(TermTuple.fromVars(x1.of(univ), x2.of(univ)), ExprConstant.IDEN), context);
        assertEquals(Term.mkEq(x1, x2), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_emptyness() {
        // test [[x \in none]] := false
        Var x = Term.mkVar("x");
        Term result = translator.translate(ExprElementOf.make(x.of(univ), ExprConstant.EMPTYNESS), context);
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
    public void testTranslate_min() {
        // test [[min]] := -8 when the bitwidth is 4
        when(mockScoper.getBitwidth()).thenReturn(4);
        Term result = translator.translate(ExprConstant.MIN, context);
        assertEquals(IntegerLiteral.apply(-8), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_max() {
        // test [[max]] := 7 when the bitwidth is 4
        when(mockScoper.getBitwidth()).thenReturn(4);
        Term result = translator.translate(ExprConstant.MAX, context);
        assertEquals(IntegerLiteral.apply(7), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inMin() {
        // test [[x \in min]] := x = -8 when the bitwidth is 4
        when(mockScoper.getBitwidth()).thenReturn(4);
        delegateToRealTranslator();
        AnnotatedVar x = Term.mkVar("x").of(Sort.Int());
        Term result = translator.translate(ExprElementOf.make(x, ExprConstant.MIN), context);
        assertEquals(Term.mkEq(x.variable(), IntegerLiteral.apply(-8)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_inMax() {
        // test [[x \in max]] := x = 7 when the bitwidth is 4
        when(mockScoper.getBitwidth()).thenReturn(4);
        delegateToRealTranslator();
        AnnotatedVar x = Term.mkVar("x").of(Sort.Int());
        Term result = translator.translate(ExprElementOf.make(x, ExprConstant.MAX), context);
        assertEquals(Term.mkEq(x.variable(), IntegerLiteral.apply(7)), result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_next() {
        // test [[(x1, x2) \in next]] := x1 != 7 && x1 + 1 = x2 for bitwidth 4
        when(mockScoper.getBitwidth()).thenReturn(4);
        Var x1 = Term.mkVar("x1"), x2 = Term.mkVar("x2");
        Term result = translator.translate(ExprElementOf.make(
                TermTuple.fromVars(x1.of(Sort.Int()), x2.of(Sort.Int())), ExprConstant.NEXT), context);
        Term expected = Term.mkAnd(
                Term.mkNot(Term.mkEq(x1, IntegerLiteral.apply(7))),
                Term.mkEq(Term.mkPlus(x1, IntegerLiteral.apply(1)), x2));
        assertEquals(expected, result);
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
    public void testTranslate_elementOfNoop() {
        // test [[x \in NOOP(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x.of(univ), ExprUnary.Op.NOOP.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_elementOfNestedNoop() {
        // test [[x \in NOOP(NOOP(e))]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x.of(univ), ExprUnary.Op.NOOP.make(null,
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
        ExprVar e = makeTestVarWithType("e", Type.smallIntType());
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        Term result = translator.translate(ExprUnary.Op.CAST2SIGINT.make(null, e), context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_elementOfCast2int() {
        // test cast2int is ignored: [[x \in cast2int(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x.of(univ), ExprUnary.Op.CAST2INT.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_elementOfCast2sigint() {
        // test cast2sigint is ignored: [[x \in cast2sigint(e)]] := [[x \in e]]
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagE);

        Expr testExpr = ExprElementOf.make(x.of(univ), ExprUnary.Op.CAST2SIGINT.make(null, e));
        Term result = translator.translate(testExpr, context);
        assertEquals(flagE, result);
        assertContextEmpty();
    }

    @Test
    public void testTranslate_multMarker() {
        // test multiplicity markers (ONEOF, SETOF, etc) are ignored when translating on their own:
        // [[ONEOF(e)]] := [[e]] and same for other multiplicity markers
        List<ExprUnary.Op> multMarkers = Arrays.asList(
                ExprUnary.Op.ONEOF,
                ExprUnary.Op.LONEOF,
                ExprUnary.Op.SOMEOF,
                ExprUnary.Op.SETOF,
                ExprUnary.Op.EXACTLYOF);
        ExprVar e = makeTestVariable("e");
        Var flagE = makeFlagConstant("flagE");
        when(mockRoot.translate(eq(e), any())).thenReturn(flagE);
        for (ExprUnary.Op marker : multMarkers) {
            Term result = translator.translate(marker.make(null, e), context);
            assertEquals(flagE, result);
            assertContextEmpty();
        }
    }

    @Test
    public void testTranslate_elementOfMultMarker() {
        // test multiplicity markers (ONEOF, SETOF, etc) are ignored when translating on their own:
        // [[x \in ONEOF(e)]] := [[x \in e]] and same for other multiplicity markers
        List<ExprUnary.Op> multMarkers = Arrays.asList(
                ExprUnary.Op.ONEOF,
                ExprUnary.Op.LONEOF,
                ExprUnary.Op.SOMEOF,
                ExprUnary.Op.SETOF,
                ExprUnary.Op.EXACTLYOF);
        ExprVar e = makeTestVariable("e");
        Var flagInE = makeFlagConstant("flagE");
        Var x = Term.mkVar("x");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(x.of(univ), e))), any()))
                .thenReturn(flagInE);
        for (ExprUnary.Op marker : multMarkers) {
            Expr testExpr = ExprElementOf.make(x.of(univ), marker.make(null, e));
            Term result = translator.translate(testExpr, context);
            assertEquals(flagInE, result);
            assertContextEmpty();
        }
    }

}
