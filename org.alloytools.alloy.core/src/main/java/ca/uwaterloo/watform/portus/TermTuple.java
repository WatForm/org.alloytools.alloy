package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstSet;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * A tuple of Fortress terms annotated with their sorts, with a bunch of convenience methods.
 */
final class TermTuple {

    private final ConstList<AnnotatedTerm> terms;

    public TermTuple(Iterable<AnnotatedTerm> terms) {
        this.terms = ConstList.make(terms);
    }

    public TermTuple(AnnotatedTerm... terms) {
        this(Arrays.asList(terms));
    }

    public TermTuple(Term term, Sort sort, List<AnnotatedVar> freeVars) {
        this(new AnnotatedTerm(term, sort, freeVars));
    }

    public static TermTuple fromVars(Iterable<AnnotatedVar> vars) {
        return new TermTuple(ConstList.make(StreamSupport.stream(vars.spliterator(), false)
                .map(AnnotatedTerm::new)
                .collect(Collectors.toList())));
    }

    public static TermTuple fromVars(AnnotatedVar... vars) {
        return TermTuple.fromVars(Arrays.asList(vars));
    }

    public ConstList<Term> getTerms() {
        return ConstList.make(terms.stream().map(AnnotatedTerm::getTerm).collect(Collectors.toList()));
    }

    public Term getTerm(int idx) {
        return getAnnotatedTerm(idx).getTerm();
    }

    public ConstList<AnnotatedTerm> getAnnotatedTerms() {
        return terms;
    }

    public AnnotatedTerm getAnnotatedTerm(int idx) {
        return terms.get(idx);
    }

    public ConstList<Sort> getSorts() {
        return ConstList.make(terms.stream()
                .map(AnnotatedTerm::getSort)
                .collect(Collectors.toList()));
    }

    public Sort getSort(int idx) {
        return getAnnotatedTerm(idx).getSort();
    }

    /** Compute the set of all free variables in all the terms in the tuple. */
    public ConstSet<AnnotatedVar> getAllFreeVars() {
        return ConstSet.make(terms.stream()
                .map(AnnotatedTerm::getFreeVars)
                .map(HashSet::new) // make them mutable to union them
                .reduce(new HashSet<>(), (set1, set2) -> {
                    set1.addAll(set2);
                    return set1;
                }));
    }

    public int size() {
        return terms.size();
    }

    public TermTuple concat(TermTuple tuple) {
        // our vars and then their vars
        return new TermTuple(Stream.concat(terms.stream(), tuple.terms.stream()).collect(Collectors.toList()));
    }

    public TermTuple slice(int fromInclusive, int toExclusive) {
        return new TermTuple(new ArrayList<>(terms.subList(fromInclusive, toExclusive)));
    }

    public TermTuple pick(int idx) {
        return slice(idx, idx + 1);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TermTuple termTuple = (TermTuple) o;
        return Objects.equals(terms, termTuple.terms);
    }

    @Override
    public int hashCode() {
        return Objects.hash(terms);
    }

}
