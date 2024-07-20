package ca.uwaterloo.watform.portus;

import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * An AnnotatedTerm that always has sort Bool.
 * Contains helper functions for combining boolean terms while maintaining the free variables list.
 */
final class BoolTerm extends AnnotatedTerm {

    public static final BoolTerm TRUE = new BoolTerm(Term.mkTop());

    public BoolTerm(Term term, Iterable<AnnotatedVar> freeVars) {
        super(term, Sort.Bool(), freeVars);
    }

    public BoolTerm(Term term) {
        super(term, Sort.Bool());
    }

    public BoolTerm(AnnotatedVar annotatedVar) {
        super(annotatedVar);
        if (!annotatedVar.sort().equals(Sort.Bool())) {
            throw new IllegalArgumentException("Invalid BoolTerm: not a boolean!");
        }
    }

    public BoolTerm and(BoolTerm other) {
        return new BoolTerm(
                Term.mkAnd(getTerm(), other.getTerm()),
                SetOps.union(getFreeVars(), other.getFreeVars()));
    }

}
