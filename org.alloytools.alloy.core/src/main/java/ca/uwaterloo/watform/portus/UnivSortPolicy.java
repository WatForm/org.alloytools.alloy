package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfind.ModelFinder;
import fortress.msfol.Sort;
import fortress.msfol.Theory;
import fortress.problemstate.ExactScope;
import fortress.problemstate.Scope;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A simple sort policy which assigns everything to a single univ sort, except for integers, which it assigns
 * to the built-in Int sort. Immutable.
 */
final class UnivSortPolicy extends SortPolicy {

    private final Sort univ;
    private final int univScope;
    private final int bitwidth;

    public UnivSortPolicy(Iterable<Sig> sigs, ScopeComputer scoper) {
        this(Sort.mkSortConst("univ"), sigs, scoper);
    }

    /** Pass in the univ sort for testing purposes. */
    UnivSortPolicy(Sort univ, Iterable<Sig> sigs, ScopeComputer scoper) {
        super(sigs);
        this.univ = univ;
        this.bitwidth = scoper.getBitwidth();

        // Determine the scope of univ: the sum of all the top-level sorts' max scopes.
        int univScope = 0;
        for (Sig sig : sigs) {
            // Don't count subsigs and don't count builtins like univ,Int,String
            if (sig.isTopLevel() && !sig.builtin) {
                univScope += scoper.sig2scope(sig);
            }
        }
        // Make sure the sort is non-empty, even if there are no sigs in the model
        this.univScope = Math.max(univScope, 1);
    }

    @Override
    public Sort getSort(Sig sig) {
        if (sig == Sig.SIGINT || sig == Sig.SEQIDX) {
            return Sort.Int();
        } else if (sig == Sig.UNIV || sig == Sig.NONE) {
            // we can't assign sorts to univ or none, but we can check if any element is in them
            return null;
        } else {
            return univ;
        }
    }

    @Override
    public int getSortScope(Sort sort) {
        if (univ.equals(sort)) {
            return univScope;
        } else if (Sort.Int().equals(sort)) {
            return bitwidth; // careful! not the number of integers (2^bitwidth)!
        } else {
            throw new ErrorFatal("Unknown sort: " + sort);
        }
    }

    @Override
    public Theory addSortsToTheory(Theory theory) {
        return theory.withSort(univ);
    }

    @Override
    public Map<Sort, Scope> getSortToScopeMap(Set<Sort> unchangingSorts) {
        Map<Sort, Scope> map = new HashMap<>();
        map.put(univ, ExactScope.apply(univScope, unchangingSorts.contains(univ)));
        // TODO - allow configuring modular vs unbounded ints?
        map.put(Sort.Int(), ExactScope.apply(bitwidth, unchangingSorts.contains(Sort.Int())));
        return map;
    }

}
