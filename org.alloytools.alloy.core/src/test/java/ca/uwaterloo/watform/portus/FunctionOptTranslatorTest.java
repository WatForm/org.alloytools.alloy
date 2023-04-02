package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;
import org.mockito.stubbing.Answer;

import java.util.ArrayList;

import static ca.uwaterloo.watform.portus.FortressASTMatcher.isAlphaEquivalentTerm;
import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class FunctionOptTranslatorTest {

    // Some test sorts
    private final Sort sortA = Sort.mkSortConst("sortA");
    private final Sort sortB = Sort.mkSortConst("sortB");

    private Translator mockRoot;

    private SortPolicy mockSortPolicy;
    private RangeAssigner mockRangeAssigner;
    private TranslationContext context;

    /** For use in Mockito then() with a translate() call: map (x1,...,xn) \in expr to funcName(x1,...,xn). */
    private Answer<Term> useTestFunction(String funcName, Expr expr) {
        return ctx -> {
            Expr argExpr = ctx.getArgument(0);
            assertTrue(argExpr instanceof ExprElementOf);
            ExprElementOf elementOf = (ExprElementOf) argExpr;
            assertEquals(expr, elementOf.sub);
            return Term.mkApp(funcName, elementOf.tuple.getVars());
        };
    }

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(
                Theory.empty().withSort(sortA).withSort(sortB).withSort(Sort.Int()));
        mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_inapplicable() {
        // test "sig A { f: set B }" doesn't apply the opt
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.setOf());
        Translator translator = new FunctionOptTranslator(mockRoot, true);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_lone_inapplicable() {
        // test "sig A { f: lone B }" doesn't apply the opt when it's off
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        Sig.Field field = sigA.addField("f", sigB.loneOf());
        Translator translator = new FunctionOptTranslator(mockRoot, false);
        assertNull(translator.translate(field, context));
    }

    @Test
    public void testTranslate_one() {
        // test translating "sig A { f: one B }" leads to:
        // - function f: sort(A)->sort(B)
        // - axiom "forall x: sort(A) . inA(x) => inB(f(x))"
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        Sig.Field field = sigA.addField("f", sigB.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true); // even when lone opt is on
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        Term result = translator.translate(field, context);
        assertNotNull(result); // opt applied

        // should have one function and one axiom
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        assertEquals(1, theory.axioms().size());

        FuncDecl func = theory.functionDeclarations().head();
        assertEquals(1, func.arity());
        assertEquals(sortA, func.argSorts().head());
        assertEquals(sortB, func.resultSort());

        Var x = Term.mkVar("x0_0");
        Term expectedAxiom = Term.mkForall(x.of(sortA), Term.mkImp(
                Term.mkApp("inA", x),
                Term.mkApp("inB", Term.mkApp(func.name(), x))));
        assertThat(theory.axioms().head(), isAlphaEquivalentTerm(expectedAxiom));
    }

    @Test
    public void testTranslate_intJoin_boundVar() {
        // test [[x.y]] := (true & inA(x)) => y(x) else 0 with "sig A {y: Int}"
        // the redundant true comes from conveniences in FunctionOptTranslator
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        Sig.Field intField = sigA.addField("y", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA));

        // put it in the system and get the generated function name
        assertNotNull(translator.translate(intField, context));
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        FuncDecl func = theory.functionDeclarations().head();

        AnnotatedVar x = Term.mkVar("x").of(sortA);
        context.addVarMapping("x", x);
        ExprHasName alloyVar = sigA.oneOf("x").names.get(0);
        Term result = translator.translate(alloyVar.join(intField), context);

        Term expected = Term.mkIfThenElse(
                Term.mkAnd(Term.mkTop(), Term.mkApp("inA", x.variable())),
                Term.mkApp(func.name(), x.variable()),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_intJoin_oneSig() {
        // test [[A.y]] := (true & inA(@1)) => y(@1) else 0 with "one sig A {y: Int}", where @1 is the domain element
        // of sort(A), and the redundant true comes from conveniences in FunctionOptTranslator
        // could be optimized better by a proper one sig optimization, but eh
        Sig.PrimSig sigA = new Sig.PrimSig("A", Attr.ONE);
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any())).thenReturn(new Pair<>(1, 1));
        Sig.Field intField = sigA.addField("y", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA));

        // put it in the system and get the generated function name
        assertNotNull(translator.translate(intField, context));
        Theory theory = context.getTheory();
        assertEquals(1, theory.functionDeclarations().size());
        FuncDecl func = theory.functionDeclarations().head();

        Term result = translator.translate(sigA.join(intField), context);
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(Term.mkTop(), Term.mkApp("inA", Term.mkDomainElement(1, sortA))),
                Term.mkApp(func.name(), Term.mkDomainElement(1, sortA)),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_intJoin_twoJoins() {
        // test [[x.y.z]] := ((true & inA(x)) & inB(y(x))) => z(y(x)) else 0
        // with sig A { y: B } and sig B { z: Int }
        // again, the redundant true comes from conveniences in FunctionOptTranslator
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB);
        when(mockSortPolicy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        Sig.Field fieldY = sigA.addField("y", sigB);
        Sig.Field fieldZ = sigB.addField("z", Sig.SIGINT.oneOf());

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inInt", Sig.SIGINT))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));

        // put the fields in the system and get the generated function names
        assertNotNull(translator.translate(fieldY, context));
        assertNotNull(translator.translate(fieldZ, context));
        Theory theory = context.getTheory();
        assertEquals(2, theory.functionDeclarations().size());
        FuncDecl funcY = theory.functionDeclarations().head();
        FuncDecl funcZ = theory.functionDeclarations().last();

        AnnotatedVar x = Term.mkVar("x").of(sortA);
        context.addVarMapping("x", x);
        ExprHasName alloyVar = sigA.oneOf("x").names.get(0);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyVar.join(fieldY).join(fieldZ), context);

        Term expected = Term.mkIfThenElse(
                Term.mkAnd(
                        Term.mkAnd(Term.mkTop(), Term.mkApp("inA", x.variable())),
                        Term.mkApp("inB", Term.mkApp(funcY.name(), x.variable()))),
                Term.mkApp(funcZ.name(), Term.mkApp(funcY.name(), x.variable())),
                IntegerLiteral.apply(0));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_integer() {
        // test [[2 = 3]] := true => (true && 2 = 3) else !true
        // the extraneous trues come from the guard clauses which are unnecessary in this case
        Term flagTwo = Term.mkVar("two");
        Term flagThree = Term.mkVar("three");
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(2))), any())).thenReturn(flagTwo);
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(3))), any())).thenReturn(flagThree);

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        Term result = translator.translate(ExprConstant.makeNUMBER(2).equal(ExprConstant.makeNUMBER(3)), context);

        Term expected = Term.mkIfThenElse(Term.mkTop(),
                Term.mkAnd(Term.mkTop(), Term.mkEq(flagTwo, flagThree)),
                Term.mkNot(Term.mkTop()));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_integerWithNoopWrappers() {
        // like the above, but wrap 2 and 3 in a variety of noop, cast2int, cast2sigint
        Term flagTwo = Term.mkVar("two");
        Term flagThree = Term.mkVar("three");
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(2))), any())).thenReturn(flagTwo);
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(3))), any())).thenReturn(flagThree);

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        Expr two = ExprUnary.Op.NOOP.make(null, ExprConstant.makeNUMBER(2).cast2int().cast2sigint().cast2int());
        Expr three = ExprUnary.Op.NOOP.make(null, ExprConstant.makeNUMBER(3)).cast2sigint();
        Term result = translator.translate(two.equal(three), context);

        Term expected = Term.mkIfThenElse(Term.mkTop(),
                Term.mkAnd(Term.mkTop(), Term.mkEq(flagTwo, flagThree)),
                Term.mkNot(Term.mkTop()));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarIn_integer() {
        // test [[2 = 3]] := true => true && 2 = 3
        // the extraneous trues come from the guard clauses which are unnecessary in this case
        Term flagTwo = Term.mkVar("two");
        Term flagThree = Term.mkVar("three");
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(2))), any())).thenReturn(flagTwo);
        when(mockRoot.translate(argThat(isSameAs(ExprConstant.makeNUMBER(3))), any())).thenReturn(flagThree);

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        Term result = translator.translate(ExprConstant.makeNUMBER(2).in(ExprConstant.makeNUMBER(3)), context);

        Term expected = Term.mkImp(Term.mkTop(),
                Term.mkAnd(Term.mkTop(), Term.mkEq(flagTwo, flagThree)));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_oneSig() {
        // test [[A = B]] := true => (true && A = B) else !true where A and B are one sigs
        // again the extraneous trues are from guard clauses
        Sig sigA = new Sig.PrimSig("A", Attr.ONE);
        Sig sigB = new Sig.PrimSig("B", Attr.ONE);
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortA); // use same sort to not short-circuit
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any()))
                .thenReturn(new Pair<>(2, 2));
        when(mockRangeAssigner.getDomainElementRange(eq(sigB), any()))
                .thenReturn(new Pair<>(3, 3));

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        Term result = translator.translate(sigA.equal(sigB), context);

        Term expected = Term.mkIfThenElse(Term.mkTop(),
                Term.mkAnd(Term.mkTop(), Term.mkEq(Term.mkDomainElement(2, sortA), Term.mkDomainElement(3, sortA))),
                Term.mkNot(Term.mkTop()));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_oneSigShortCircuit() {
        // test [[A = B]] := false where A and B are one sigs from different sorts
        Sig sigA = new Sig.PrimSig("A", Attr.ONE);
        Sig sigB = new Sig.PrimSig("B", Attr.ONE);
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortB); // use different sort to short-circuit
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any()))
                .thenReturn(new Pair<>(2, 2));
        when(mockRangeAssigner.getDomainElementRange(eq(sigB), any()))
                .thenReturn(new Pair<>(3, 3));

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        Term result = translator.translate(sigA.equal(sigB), context);
        assertEquals(Term.mkBottom(), result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_boundVar() {
        // test [[x = y]] := true => (true && x = y) else !true where x and y are scalar variables of the same sort
        // again the extraneous trues are from guard clauses
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var fortressX = Term.mkVar("x");
        Var fortressY = Term.mkVar("y");
        // Use the same sort so we don't short-circuit
        context.addVarMapping("x", fortressX.of(sortA));
        context.addVarMapping("y", fortressY.of(sortA));

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);

        Term expected = Term.mkIfThenElse(Term.mkTop(),
                Term.mkAnd(Term.mkTop(), Term.mkEq(fortressX, fortressY)),
                Term.mkNot(Term.mkTop()));
        assertEquals(expected, result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_boundVarShortCircuit() {
        // test [[x = y]] := false where x and y are scalar variables of different sorts
        ExprVar alloyX = ExprVar.make(null, "x");
        ExprVar alloyY = ExprVar.make(null, "y");
        Var fortressX = Term.mkVar("x");
        Var fortressY = Term.mkVar("y");
        // Use different sorts to short-circuit
        context.addVarMapping("x", fortressX.of(sortA));
        context.addVarMapping("y", fortressY.of(sortB));

        Translator translator = new FunctionOptTranslator(mockRoot, true);
        //noinspection SuspiciousNameCombination
        Term result = translator.translate(alloyX.equal(alloyY), context);
        assertEquals(Term.mkBottom(), result);
    }

    @Test
    public void testTranslate_optimizedScalarEquals_join() {
        // test [[A.x = B.y]] := (true && inA(@1)) => (true && inB(@2)) && x(@1) = y(@2) else !(true && inB(@2))
        Sig sigA = new Sig.PrimSig("A", Attr.ONE);
        Sig sigB = new Sig.PrimSig("B", Attr.ONE);
        when(mockSortPolicy.getSort(sigA)).thenReturn(sortA);
        when(mockSortPolicy.getSort(sigB)).thenReturn(sortA); // same sort for simplicity
        when(mockRangeAssigner.getDomainElementRange(eq(sigA), any()))
                .thenReturn(new Pair<>(1, 1));
        when(mockRangeAssigner.getDomainElementRange(eq(sigB), any()))
                .thenReturn(new Pair<>(2, 2));

        when(mockRoot.translate(any(), any()))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inB", sigB))
                .then(useTestFunction("inA", sigA))
                .then(useTestFunction("inB", sigB));
        Translator translator = new FunctionOptTranslator(mockRoot, true);

        // Translate the x and y fields to prime the context
        Sig.Field x = sigA.addField("x", sigA.oneOf());
        Sig.Field y = sigB.addField("y", sigB.oneOf());
        assertNotNull(translator.translate(x, context));
        assertNotNull(translator.translate(y, context));

        // Extract the function names for x and y
        Theory theory = context.getTheory();
        assertEquals(2, theory.functionDeclarations().size());
        FuncDecl funcX = theory.functionDeclarations().head();
        FuncDecl funcY = theory.functionDeclarations().last();

        //noinspection SuspiciousNameCombination
        Term result = translator.translate(sigA.join(x).equal(sigB.join(y)), context);
        Term expected = Term.mkIfThenElse(
                Term.mkAnd(Term.mkTop(), Term.mkApp("inA", Term.mkDomainElement(1, sortA))),
                Term.mkAnd(
                        Term.mkAnd(Term.mkTop(), Term.mkApp("inB", Term.mkDomainElement(2, sortA))),
                        Term.mkEq(
                                Term.mkApp(funcX.name(), Term.mkDomainElement(1, sortA)),
                                Term.mkApp(funcY.name(), Term.mkDomainElement(2, sortA)))),
                Term.mkNot(Term.mkAnd(Term.mkTop(), Term.mkApp("inB", Term.mkDomainElement(2, sortA)))));
        assertEquals(expected, result);
    }

}
