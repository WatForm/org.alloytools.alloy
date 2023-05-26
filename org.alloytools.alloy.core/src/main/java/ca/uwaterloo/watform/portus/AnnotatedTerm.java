package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstSet;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.Collections;
import java.util.Objects;

/**
 * A Fortress Term annotated with sort data, effectively generalizing {@link AnnotatedVar}.
 */
final class AnnotatedTerm {

    private final Term term;
    private final Sort sort;

    /**
     * A set of the free variables that appear in the term along with their sorts.
     * The Fortress Term AST doesn't store sort information along with Vars,
     * so we store the information conveniently here.
     */
    private final ConstSet<AnnotatedVar> freeVars;

    /**
     * Construct an annotated term. {@code freeVars} must be the list of Vars that appear
     * free in {@code term}, although we don't verify this.
     */
    public AnnotatedTerm(Term term, Sort sort, Iterable<AnnotatedVar> freeVars) {
        this.term = term;
        this.sort = sort;
        this.freeVars = ConstSet.make(freeVars);
    }

    /**
     * Construct an annotated term, assuming there are no free variables.
     */
    public AnnotatedTerm(Term term, Sort sort) {
        this(term, sort, Collections.emptyList());
    }

    /**
     * Construct an annotated term from an annotated var. It is taken to be the only free variable.
     */
    public AnnotatedTerm(AnnotatedVar annotatedVar) {
        this(annotatedVar.variable(), annotatedVar.sort(), Collections.singleton(annotatedVar));
    }

    public Term getTerm() {
        return term;
    }

    public Sort getSort() {
        return sort;
    }

    /** Get the set of free variables that appear in the term. */
    public ConstSet<AnnotatedVar> getFreeVars() {
        return freeVars;
    }

    @Override
    public String toString() {
        return term + ": " + sort;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AnnotatedTerm that = (AnnotatedTerm) o;
        return Objects.equals(term, that.term) && Objects.equals(sort, that.sort);
    }

    @Override
    public int hashCode() {
        return Objects.hash(term, sort);
    }

}
