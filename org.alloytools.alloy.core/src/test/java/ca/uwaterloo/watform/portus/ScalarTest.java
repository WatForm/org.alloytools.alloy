package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class ScalarTest {

    private TranslationContext context;

    @Before
    public void setUp() {
        ScopeComputer scoper = mock(ScopeComputer.class);
        SortPolicy sortPolicy = mock(SortPolicy.class);
        when(sortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty());
        RangeAssigner rangeAssigner = mock(RangeAssigner.class);
        context = new TranslationContext(new PortusOptions(), scoper, sortPolicy, rangeAssigner);
    }

    @Test
    public void testCompose_nilaryNilary_error() {
        // can't compose nilaries together
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var guardF = Term.mkVar("guardF");
        context.addFortressVar(x.of(sort));

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF, context);
        Scalar g = new Scalar(new AnnotatedTerm(x.of(sort)), guardF, context);
        assertThrows(ErrorFatal.class, () -> Scalar.compose(f, g, context.getVarMappingContext()));
    }

    @Test
    public void testCompose_nilaryUnary() {
        // compose(x, f) == f(x) when f is unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var guardF = Term.mkVar("guardF");
        context.addFortressVar(x.of(sort));

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF, context);
        Scalar g = new Scalar(Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0)), context);

        Scalar composition = Scalar.compose(f, g, context.getVarMappingContext());
        assertEquals(0, composition.getArity());
        assertTrue(composition.isNilary());
        assertTrue(composition.getArgSorts().isEmpty());
        assertEquals(Term.mkApp("g", x), composition.getNilaryScalar(context));
        assertEquals(sort, composition.getResultSort());
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x)), composition.getNilaryGuard(context));
    }

    @Test
    public void testCompose_unaryUnary() {
        // compose(f, g) == x |-> g(f(x)) when both are unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        context.addFortressVar(x.of(sort));

        Scalar f = new Scalar(Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardF", tuple.getTerm(0)), context);
        Scalar g = new Scalar(Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0)), context);

        Scalar composition = Scalar.compose(f, g, context.getVarMappingContext());
        assertEquals(1, composition.getArity());
        assertFalse(composition.isNilary());
        assertEquals(1, composition.getArgSorts().size());
        assertEquals(sort, composition.getArgSorts().get(0));
        Term scalar = composition.getScalar(TermTuple.fromVars(x.of(sort)), context);
        assertEquals(Term.mkApp("g", Term.mkApp("f", x)), scalar);
        assertEquals(sort, composition.getResultSort());
        Term guard = composition.getGuard(TermTuple.fromVars(x.of(sort)), context);
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x))), guard);
    }

    @Test
    public void testCompose_nilaryBinary() {
        // compose(x, f) == y |-> f(x,y) when f is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardF = Term.mkVar("guardF");
        context.addFortressVars(x.of(sort), y.of(sort));

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF, context);
        Scalar g = new Scalar(Arrays.asList(sort, sort), sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0), tuple.getTerm(1)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0), tuple.getTerm(1)), context);

        Scalar composition = Scalar.compose(f, g, context.getVarMappingContext());
        assertEquals(1, composition.getArity());
        assertFalse(composition.isNilary());
        assertEquals(1, composition.getArgSorts().size());
        assertEquals(sort, composition.getArgSorts().get(0));
        Term scalar = composition.getScalar(TermTuple.fromVars(y.of(sort)), context);
        assertEquals(Term.mkApp("g", x, y), scalar);
        assertEquals(sort, composition.getResultSort());
        Term guard = composition.getGuard(TermTuple.fromVars(y.of(sort)), context);
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x, y)), guard);
    }

    @Test
    public void testCompose_unaryBinary() {
        // compose(f, g) == x,y |-> g(f(x),y) when f is unary and g is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        context.addFortressVars(x.of(sort), y.of(sort));

        Scalar f = new Scalar(Collections.singletonList(sort), sort,
                tuple -> Term.mkApp("f", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardF", tuple.getTerm(0)), context);
        Scalar g = new Scalar(Arrays.asList(sort, sort), sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0), tuple.getTerm(1)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0), tuple.getTerm(1)), context);

        Scalar composition = Scalar.compose(f, g, context.getVarMappingContext());
        assertEquals(2, composition.getArity());
        assertFalse(composition.isNilary());
        assertEquals(2, composition.getArgSorts().size());
        assertEquals(sort, composition.getArgSorts().get(0));
        assertEquals(sort, composition.getArgSorts().get(1));
        Term scalar = composition.getScalar(TermTuple.fromVars(x.of(sort), y.of(sort)), context);
        assertEquals(Term.mkApp("g", Term.mkApp("f", x), y), scalar);
        assertEquals(sort, composition.getResultSort());
        Term guard = composition.getGuard(TermTuple.fromVars(x.of(sort), y.of(sort)), context);
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x), y)), guard);
    }

}
