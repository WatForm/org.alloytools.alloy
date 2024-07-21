package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * A range assigner is in charge of assigning ranges of domain elements to signatures.
 * @see #getDomainElementRange(Sig) 
 */
class RangeAssigner {

    private final List<Sig> allSigs;
    private final SortPolicy sortPolicy;
    private final ScopeComputer scoper;

    // Keep state: which sigs have we added DE axioms for, so we don't add duplicates?
    private final Set<Sig> sigsWithDEAxioms;

    // Memoize getDomainElementRange() for performance reasons.
    // It's valid to do this because getDomainElementRange() is a pure function, since it only depends
    // on sortPolicy and scoper which *should* be fixed.
    private final Map<Sig, Pair<Integer, Integer>> memoizedSigToDERange;

    public RangeAssigner(Iterable<Sig> allSigs, SortPolicy sortPolicy, ScopeComputer scoper) {
        this.allSigs = PortusUtil.iterableToList(allSigs);
        this.sortPolicy = sortPolicy;
        this.scoper = scoper;
        this.sigsWithDEAxioms = new HashSet<>();
        this.memoizedSigToDERange = new HashMap<>();
    }

    public RangeAssigner(RangeAssigner other) {
        // Deep copy so changes in the copy don't affect the original
        this.allSigs = new ArrayList<>(other.allSigs);
        this.sortPolicy = other.sortPolicy; // sort policy is immutable
        this.scoper = other.scoper; // we probably don't mutate it...
        this.sigsWithDEAxioms = new HashSet<>(other.sigsWithDEAxioms);
        this.memoizedSigToDERange = new HashMap<>(other.memoizedSigToDERange);
    }

    /**
     * Get the inclusive range of domain element indices in the sort spanned by the sig.
     * May be null if an exact domain element range cannot be determined.
     * To ensure that the domain elements in the range actually are assigned to the sig,
     * call {@link #addRangeAxiom(Sig, Translator, TranslationContext)}.
     *
     * WARNING: If sig has a non-exact scope, we return a range of the minimum size that is forced by any child with an
     * exact scope. (For example, if A has a non-exact scope but its (only) child A1 has an exact scope of 2, we return
     * a range of size 2 for A.) <b>This result should not be relied upon except to find the domain element ranges of
     * those children with exact scopes - check if sig is exact before using this function.</b>
     *
     * Only exact-scope children are taken into account; non-exact children are ignored. This means that the list of
     * domain elements arranged by number will have all the assigned DEs of the exact-scope sigs bunched up at the
     * beginning, with the DEs which are fluid between non-exact-scope sigs at the end. This ensures that each exact-
     * scope sig has a continuous range of DEs which fits in the actual list of DEs.
     */
    public Pair<Integer, Integer> getDomainElementRange(Sig sig) {
        if (!(sig instanceof Sig.PrimSig)) {
            // TODO: can we support subset sigs?
            return null;
        }
        if (sig == Sig.SIGINT) {
            // domain elements of Int are special, so we don't support them
            return null;
        }
        if (memoizedSigToDERange.containsKey(sig)) {
            // We've computed it before, return the precomputed value
            return memoizedSigToDERange.get(sig);
        }

        Sig.PrimSig primSig = (Sig.PrimSig) sig;
        Sort sort = sortPolicy.getSort(primSig);
        if (sort == null) {
            // they've passed in something we can't deal with
            return null;
        }
        int sigScope = getMinimumSize(primSig, scoper);

        List<Sig.PrimSig> siblings = allSigs.stream()
                .filter(otherSig -> otherSig instanceof Sig.PrimSig)
                .map(otherSig -> (Sig.PrimSig) otherSig)
                // We don't support strings yet, so explicitly ignore them here, since sig2scope will give -1
                // if the scope isn't specified (which is the case for strings)
                .filter(otherSig -> otherSig != Sig.STRING)
                .filter(otherSig -> primSig.isTopLevel()
                        ? otherSig.isTopLevel() && sort.equals(sortPolicy.getSort(otherSig))
                        : primSig.parent == otherSig.parent)
                .sorted(Comparator.comparing(s -> s.label)) // hopefully the labels are unique
                .collect(Collectors.toList());

        // the list should include primSig (so shouldn't be empty)
        assert siblings.contains(primSig);

        // find the start of our range according to our parent/siblings
        int domainElementStart;
        if (primSig == siblings.get(0)) {
            // If we're the first of our siblings, we start in the parent's range
            if (primSig.isTopLevel()) {
                domainElementStart = 1; // the range of the univ sig starts at 1
            } else {
                Pair<Integer, Integer> parentRange = getDomainElementRange(primSig.parent);
                if (parentRange == null) {
                    // We can't get the range of the parent sig, so we can't get the range of this sig
                    return null;
                }
                domainElementStart = parentRange.a;
            }
        } else {
            // Otherwise, go after the range of the closest sibling behind us with a valid range
            // (Note this will always succeed since siblings contains primSig and we checked it isn't first)
            int primSigIdx = siblings.indexOf(primSig);
            Pair<Integer, Integer> prevSiblingRange = getDomainElementRange(siblings.get(primSigIdx - 1));
            domainElementStart = prevSiblingRange.b + 1;
        }

        Pair<Integer, Integer> deRange = new Pair<>(domainElementStart, domainElementStart + sigScope - 1);
        memoizedSigToDERange.put(sig, deRange);
        return deRange;
    }

    private int getMinimumSize(Sig.PrimSig sig, ScopeComputer scoper) {
        if (scoper.isExact(sig)) {
            return scoper.sig2scope(sig);
        } else {
            // use the sum of all the children's minimum sizes, because it's the size that the children with
            // exact scopes will force this sig to be at least
            int minSize = 0;
            for (Sig.PrimSig child : sig.children()) {
                minSize += getMinimumSize(child, scoper);
            }
            return minSize;
        }
    }

    /**
     * Add an axiom to the context stating that the elements of the domain element range for this sig all belong
     * to this sig. This must be called for any sig for which we rely on the domain element range.
     * This object handles not adding duplicate axioms.
     */
    public void addRangeAxiom(Sig sig, Translator translator, TranslationContext context) {
        if (sig.builtin) {
            // Sanity check - we should never try to add a range axiom for a builtin sig
            throw new ErrorFatal("Can't add range axiom for builtin sig!");
        }

        Pair<Integer, Integer> range = getDomainElementRange(sig);
        if (range == null) {
            return; // Don't bother if we can't assign a range
        }

        // Don't add duplicate axioms
        if (sigsWithDEAxioms.contains(sig)) {
            return;
        }
        sigsWithDEAxioms.add(sig);

        // TODO there's some room for optimization here: if a parent and a child both have axioms for their DE
        // ranges specified, then the parent one is redundant due to the inChild => inParent axiom.
        // But I don't know if that would save any time in the SMT solver.
        List<Term> conjuncts = new ArrayList<>();
        Sort sort = sortPolicy.getSort(sig);
        for (int deIdx = range.a; deIdx <= range.b; deIdx++) {
            Term deInSig = getDEInSigAxiom(sig, deIdx, sort, translator, context);
            conjuncts.add(deInSig);
        }

        if (conjuncts.isEmpty()) {
            // Just in case they pass an empty range
            return;
        }
        Term axiom = Term.mkAnd(conjuncts);
        context.addAxiom(axiom);
    }

    private Term getDEInSigAxiom(Sig sig, int deIdx, Sort sort, Translator translator, TranslationContext context) {
        // [[_@deIdx \in sig]]
        AnnotatedTerm domainElement = new AnnotatedTerm(Term.mkDomainElement(deIdx, sort), sort);
        Expr axiom = ExprElementOf.make(domainElement, sig);
        return translator.translate(axiom, context);
    }

}
