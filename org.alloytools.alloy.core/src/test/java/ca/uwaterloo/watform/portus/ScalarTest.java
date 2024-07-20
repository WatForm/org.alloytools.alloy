package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import org.junit.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
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

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), new BoolTerm(guardF.of(Sort.Bool())));
        Scalar g = new Scalar(new AnnotatedTerm(x.of(sort)), new BoolTerm(guardF.of(Sort.Bool())));
        assertThrows(ErrorFatal.class, () -> Scalar.compose(f, g));
    }

    @Test
    public void testCompose_nilaryUnary() {
        // compose(x, f) == f(x) when f is unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var guardF = Term.mkVar("guardF");

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), new BoolTerm(guardF.of(Sort.Bool())));
        Scalar g = new Scalar(1,
                args -> new AnnotatedTerm(Term.mkApp("g", args.get(0).getTerm()), sort, args.get(0).getFreeVars()),
                args -> new BoolTerm(Term.mkApp("guardG", args.get(0).getTerm()), args.get(0).getFreeVars()));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(0, composition.arity());
        assertTrue(composition.isNilary());
        assertEquals(Term.mkApp("g", x), composition.getScalar().getTerm());
        assertEquals(sort, composition.getScalar().getSort());
        assertThat(composition.getScalar().getFreeVars(), containsInAnyOrder(x.of(sort)));
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x)), composition.getGuard().getTerm());
        assertThat(composition.getGuard().getFreeVars(), containsInAnyOrder(x.of(sort), guardF.of(Sort.Bool())));
    }

    @Test
    public void testCompose_unaryUnary() {
        // compose(f, g) == x |-> g(f(x)) when both are unary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");

        Scalar f = new Scalar(1,
                args -> new AnnotatedTerm(Term.mkApp("f", args.get(0).getTerm()), sort, args.get(0).getFreeVars()),
                args -> new BoolTerm(Term.mkApp("guardF", args.get(0).getTerm()), args.get(0).getFreeVars()));
        Scalar g = new Scalar(1,
                args -> new AnnotatedTerm(Term.mkApp("g", args.get(0).getTerm()), sort, args.get(0).getFreeVars()),
                args -> new BoolTerm(Term.mkApp("guardG", args.get(0).getTerm()), args.get(0).getFreeVars()));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(1, composition.arity());
        assertFalse(composition.isNilary());
        AnnotatedTerm scalar = composition.getScalar(new AnnotatedTerm(x.of(sort)));
        assertEquals(Term.mkApp("g", Term.mkApp("f", x)), scalar.getTerm());
        assertEquals(sort, scalar.getSort());
        assertThat(scalar.getFreeVars(), containsInAnyOrder(x.of(sort)));
        AnnotatedTerm guard = composition.getGuard(new AnnotatedTerm(x.of(sort)));
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x))), guard.getTerm());
        assertThat(guard.getFreeVars(), containsInAnyOrder(x.of(sort)));
    }

    @Test
    public void testCompose_nilaryBinary() {
        // compose(x, f) == y |-> f(x,y) when f is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var guardF = Term.mkVar("guardF");

        Scalar f = new Scalar(new AnnotatedTerm(x.of(sort)), new BoolTerm(guardF.of(Sort.Bool())));
        Scalar g = new Scalar(2,
                args -> new AnnotatedTerm(
                        Term.mkApp("g", args.get(0).getTerm(), args.get(1).getTerm()), sort,
                        SetOps.union(args.get(0).getFreeVars(), args.get(1).getFreeVars())),
                args -> new BoolTerm(
                        Term.mkApp("guardG", args.get(0).getTerm(), args.get(1).getTerm()),
                        SetOps.union(args.get(0).getFreeVars(), args.get(1).getFreeVars())));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(1, composition.arity());
        assertFalse(composition.isNilary());
        AnnotatedTerm scalar = composition.getScalar(new AnnotatedTerm(y.of(sort)));
        assertEquals(Term.mkApp("g", x, y), scalar.getTerm());
        assertEquals(sort, scalar.getSort());
        assertThat(scalar.getFreeVars(), containsInAnyOrder(x.of(sort), y.of(sort)));
        AnnotatedTerm guard = composition.getGuard(new AnnotatedTerm(y.of(sort)));
        assertEquals(Term.mkAnd(guardF, Term.mkApp("guardG", x, y)), guard.getTerm());
        assertThat(guard.getFreeVars(), containsInAnyOrder(x.of(sort), y.of(sort), guardF.of(Sort.Bool())));
    }

    @Test
    public void testCompose_unaryBinary() {
        // compose(f, g) == x,y |-> g(f(x),y) when f is unary and g is binary
        Sort sort = Sort.mkSortConst("S");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");

        Scalar f = new Scalar(1,
                args -> new AnnotatedTerm(Term.mkApp("f", args.get(0).getTerm()), sort, args.get(0).getFreeVars()),
                args -> new BoolTerm(Term.mkApp("guardF", args.get(0).getTerm()), args.get(0).getFreeVars()));
        Scalar g = new Scalar(2,
                args -> new AnnotatedTerm(
                        Term.mkApp("g", args.get(0).getTerm(), args.get(1).getTerm()), sort,
                        SetOps.union(args.get(0).getFreeVars(), args.get(1).getFreeVars())),
                args -> new BoolTerm(
                        Term.mkApp("guardG", args.get(0).getTerm(), args.get(1).getTerm()),
                        SetOps.union(args.get(0).getFreeVars(), args.get(1).getFreeVars())));

        Scalar composition = Scalar.compose(f, g);
        assertEquals(2, composition.arity());
        assertFalse(composition.isNilary());
        AnnotatedTerm scalar = composition.getScalar(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(y.of(sort)));
        assertEquals(Term.mkApp("g", Term.mkApp("f", x), y), scalar.getTerm());
        assertEquals(sort, scalar.getSort());
        assertThat(scalar.getFreeVars(), containsInAnyOrder(x.of(sort), y.of(sort)));
        AnnotatedTerm guard = composition.getGuard(new AnnotatedTerm(x.of(sort)), new AnnotatedTerm(y.of(sort)));
        assertEquals(Term.mkAnd(Term.mkApp("guardF", x), Term.mkApp("guardG", Term.mkApp("f", x), y)), guard.getTerm());
        assertThat(guard.getFreeVars(), containsInAnyOrder(x.of(sort), y.of(sort)));
    }

}
