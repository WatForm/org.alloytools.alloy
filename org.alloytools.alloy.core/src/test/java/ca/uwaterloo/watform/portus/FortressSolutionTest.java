package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import fortress.interpretation.BasicInterpretation;
import fortress.interpretation.Interpretation;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Value;
import org.junit.Before;
import org.junit.Test;
import scala.collection.immutable.Seq;
import scala.collection.immutable.Set$;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.instanceOf;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.withSettings;

public class FortressSolutionTest {

    private static final int NUM_UNIV_ELEMS = 3;
    private static final int INT_BITWIDTH = 4;
    private static final int NUM_INT_ELEMS = 1 << INT_BITWIDTH;

    private FortressSolution solution;

    @Before
    public void setUp() {
        Sort univ = Sort.mkSortConst("testUniv");
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        SortPolicy sortPolicy = new UnivSortPolicy(univ, new ArrayList<>(), mockScoper);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(new ArrayList<>(), sortPolicy, mockScoper));
        TranslationContext context = new TranslationContext(
                new PortusOptions(), mockScoper, sortPolicy, mockRangeAssigner);

        Map<Sort, Seq<Value>> sorts = new HashMap<>();
        List<Value> elems = new ArrayList<>();
        for (int i = 1; i <= NUM_UNIV_ELEMS; i++) {
            elems.add(Term.mkDomainElement(i, univ));
        }
        sorts.put(univ, CollectionConverters.asScala(elems).toSeq());
        List<Value> intElems = new ArrayList<>();
        for (int i = -NUM_INT_ELEMS/2; i < NUM_INT_ELEMS/2; i++) {
            intElems.add(IntegerLiteral.apply(i));
        }
        sorts.put(Sort.Int(), CollectionConverters.asScala(intElems).toSeq());
        Map<AnnotatedVar, Value> constants = new HashMap<>();
        Map<FuncDecl, scala.collection.immutable.Map<Seq<Value>, Value>> functions = new HashMap<>();
        Interpretation interpretation = new BasicInterpretation(
                PortusUtil.<Sort, Seq<Value>>toScalaMap(sorts),
                PortusUtil.<AnnotatedVar, Value>toScalaMap(constants),
                PortusUtil.<FuncDecl, scala.collection.immutable.Map<Seq<Value>, Value>>toScalaMap(functions),
                Set$.MODULE$.<FunctionDefinition>empty());

        //noinspection unchecked
        NameGenerator nameGenerator = new IntSuffixNameGenerator(
                (scala.collection.immutable.Set<String>) scala.collection.Set$.MODULE$.empty(), 0);
        TranslatorManager manager = new TranslatorManager(
                context.options, new PortusStatistics(), sortPolicy, nameGenerator);
        solution = new FortressSolution(
                interpretation, manager, context,
                Collections.singletonList(Sig.UNIV), "", "");
    }

    @Test
    public void testEval_sig() {
        // the atoms won't be distinguishable, so check their size + arity
        A4TupleSet tupleSet = solution.eval(Sig.UNIV);
        assertEquals(1, tupleSet.arity());
        assertEquals(NUM_UNIV_ELEMS + NUM_INT_ELEMS, tupleSet.size());
    }

    @Test
    public void testEval_sigXsig() {
        Object result = solution.eval(Sig.UNIV.product(Sig.UNIV));
        assertThat(result, instanceOf(A4TupleSet.class));
        A4TupleSet tupleSet = (A4TupleSet) result;
        assertEquals(2, tupleSet.arity());
        assertEquals((NUM_UNIV_ELEMS + NUM_INT_ELEMS) * (NUM_UNIV_ELEMS + NUM_INT_ELEMS), tupleSet.size());
    }

    @Test
    public void testEval_trueFormula() {
        Object result = solution.eval(ExprConstant.makeNUMBER(1).equal(ExprConstant.makeNUMBER(1)));
        assertThat(result, instanceOf(Boolean.class));
        assertTrue((boolean) result);
    }

    @Test
    public void testEval_falseFormula() {
        Object result = solution.eval(ExprConstant.makeNUMBER(1).equal(ExprConstant.makeNUMBER(2)));
        assertThat(result, instanceOf(Boolean.class));
        assertFalse((boolean) result);
    }

    @Test
    public void testEval_twiceSameUniverse() {
        // Alloy requires that the universe is consistent, otherwise it fails with a cryptic error
        A4TupleSet tupleSet1 = solution.eval(Sig.UNIV);
        A4TupleSet tupleSet2 = solution.eval(Sig.UNIV);
        assertEquals(tupleSet1.debugGetKodkodTupleset().universe(), tupleSet2.debugGetKodkodTupleset().universe());
    }

}