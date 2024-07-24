package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

public class ScalarTest {

    @Test
    public void testCompose_nilaryNilary_error() {
        // can't compose nilaries together
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var guardF = Term.mkVar("guardF");

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF);
        Scalar g = new Scalar(new AnnotatedTerm(x.of(sort)), guardF);
        assertThrows(ErrorFatal.class, () -> Scalar.compose(f, g));
    }

    @Test
    public void testCompose_nilaryUnary() {
        // compose(x, f) == f(x) when f is unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var guardF = Term.mkVar("guardF");

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF);
        Scalar g = new Scalar(1, sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0)));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(0, composition.getArity());
        assertTrue(composition.isNilary());
        assertEquals(Term.mkApp("g", x), composition.getNilaryScalar());
        assertEquals(sort, composition.getSort());
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x)), composition.getNilaryGuard());
    }

    @Test
    public void testCompose_unaryUnary() {
        // compose(f, g) == x |-> g(f(x)) when both are unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");

        Scalar f = new Scalar(1, sort,
                tuple -> Term.mkApp("f", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardF", tuple.getTerm(0)));
        Scalar g = new Scalar(1, sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0)));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(1, composition.getArity());
        assertFalse(composition.isNilary());
        Term scalar = composition.getScalar(TermTuple.fromVars(x.of(sort)));
        assertEquals(Term.mkApp("g", Term.mkApp("f", x)), scalar);
        assertEquals(sort, composition.getSort());
        Term guard = composition.getGuard(TermTuple.fromVars(x.of(sort)));
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x))), guard);
    }

    @Test
    public void testCompose_nilaryBinary() {
        // compose(x, f) == y |-> f(x,y) when f is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardF = Term.mkVar("guardF");

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), guardF);
        Scalar g = new Scalar(2, sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0), tuple.getTerm(1)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0), tuple.getTerm(1)));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(1, composition.getArity());
        assertFalse(composition.isNilary());
        Term scalar = composition.getScalar(TermTuple.fromVars(y.of(sort)));
        assertEquals(Term.mkApp("g", x, y), scalar);
        assertEquals(sort, composition.getSort());
        Term guard = composition.getGuard(TermTuple.fromVars(y.of(sort)));
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x, y)), guard);
    }

    @Test
    public void testCompose_unaryBinary() {
        // compose(f, g) == x,y |-> g(f(x),y) when f is unary and g is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");

        Scalar f = new Scalar(1, sort,
                tuple -> Term.mkApp("f", tuple.getTerm(0)),
                tuple -> Term.mkApp("guardF", tuple.getTerm(0)));
        Scalar g = new Scalar(2, sort,
                tuple -> Term.mkApp("g", tuple.getTerm(0), tuple.getTerm(1)),
                tuple -> Term.mkApp("guardG", tuple.getTerm(0), tuple.getTerm(1)));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(2, composition.getArity());
        assertFalse(composition.isNilary());
        Term scalar = composition.getScalar(TermTuple.fromVars(x.of(sort), y.of(sort)));
        assertEquals(Term.mkApp("g", Term.mkApp("f", x), y), scalar);
        assertEquals(sort, composition.getSort());
        Term guard = composition.getGuard(TermTuple.fromVars(x.of(sort), y.of(sort)));
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x), y)), guard);
    }

}
