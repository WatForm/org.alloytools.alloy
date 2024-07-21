package ca.uwaterloo.watform.portus;

import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * An AnnotatedTerm that always has sort Bool.
 */
final class BoolTerm extends AnnotatedTerm {

    public static final BoolTerm TRUE = new BoolTerm(Term.mkTop());

    public BoolTerm(Term term) {
        super(term, Sort.Bool());
    }

    public BoolTerm(AnnotatedVar annotatedVar) {
        super(annotatedVar);
        if (!annotatedVar.sort().equals(Sort.Bool())) {
            throw new IllegalArgumentException("Invalid BoolTerm: not a boolean!");
        }
    }

}
