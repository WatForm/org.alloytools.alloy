package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
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

    // Flag constants are used as mock return values of translations.
    private Term makeFlagConstant(String label) {
        return Term.mkVar(label);
    }

    private void assertIsMembershipPredicate(FuncDecl func, Sort sort, String name) {
        assertThat(func.name(), startsWith(name));
        assertThat(func.arity(), is(1));
        assertThat(func.argSorts().head(), is(sort));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    @Test
    public void testTranslate_primSig_single() {
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
        assertThat(func.name(), startsWith("inTestSig"));
        assertThat(func.arity(), is(1));
        assertThat(func.argSorts().head(), is(sort));
        assertThat(func.resultSort(), is(Sort.Bool()));
    }

    @Test
    public void testTranslate_primSig_oneExtendsWithExactScope() {
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

        Term result = translator.translate(parent, context);
        assertThat(result, is(notNullValue()));

        // should have just one sort with same name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort parentSort = context.getSigSort(parent);
        assertThat(parentSort, is(notNullValue()));
        assertThat(parentSort.name(), startsWith("Parent"));
        assertThat(context.getSortScope(parentSort), is(3));

        // create the expected exact scope axiom
        // "exists x1, x2: parent . forall y: parent. !(x1 = x2) && ([[y \in sort]] => y = x1 || y = x2)"
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var y = Term.mkVar("y");
        Term exactScopeAxiom = Term.mkExists(Arrays.asList(x1.of(parentSort), x2.of(parentSort)),
                Term.mkForall(y.of(parentSort), Term.mkAnd(
                        Term.mkNot(Term.mkEq(x1, x2)),
                        Term.mkImp(inChildFlag, Term.mkOr(
                                Term.mkEq(y, x1),
                                Term.mkEq(y, x2))))));

        // should have two axioms: subset and exact scope
        Set<Term> axioms = CollectionConverters.asJava(context.getTheory().axioms());
        assertThat(axioms, hasSize(2));
        //noinspection unchecked
        assertThat(axioms, containsInAnyOrder(
                is(subsetFlag),
                isAlphaEquivalentTerm(exactScopeAxiom)
        ));

        // should have two functions, inParent: Parent -> Bool and inChild: Parent -> Bool
        assertThat(context.getTheory().functionDeclarations().size(), is(2));
        FuncDecl inParentPred = context.getTheory().functionDeclarations().head();
        assertIsMembershipPredicate(inParentPred, parentSort, "inParent");
        FuncDecl inChildPred = context.getTheory().functionDeclarations().last();
        assertIsMembershipPredicate(inChildPred, parentSort, "inChild");
    }

}
