package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;
import fortress.msfol.Sort;
import fortress.msfol.Theory;

import java.util.*;

/**
 * A fast sort policy that just converts types to sort resolvants without recursing.
 * Useful for preprocessing when we know there is no sig hierarchy!
 */
public class TypeSortPolicy extends SortPolicy {

    private final Map<Sig.PrimSig, Sort> sigsToSort;
    private final Map<Sort, Sig.PrimSig> sortsToSig;

    private final ScopeComputer scoper;

    /** NOTE: Sig hierarchy must have been eliminated! */
    public TypeSortPolicy(List<Sig> allSigs, ScopeComputer scoper, NameGenerator nameGenerator) {
        super(allSigs);
        this.scoper = scoper;

        sigsToSort = new HashMap<>(allSigs.size());
        sortsToSig = new HashMap<>(allSigs.size());
        sigsToSort.put(Sig.SIGINT, Sort.Int());
        sortsToSig.put(Sort.Int(), Sig.SIGINT);
        for (Sig sig : allSigs) {
            if (sig instanceof Sig.PrimSig && !sig.builtin) {
                Sort sort = Sort.mkSortConst(nameGenerator.freshName("Sort_" + sig.label));
                sigsToSort.put((Sig.PrimSig) sig, sort);
                sortsToSig.put(sort, (Sig.PrimSig) sig);
            }
        }
    }

    @Override
    public SortResolvant getMinimalExprSorts(Expr expr, VarMappingContext varMappingContext) {
        Type type = expr.type();
        Set<List<Sort>> tuples = new HashSet<>(type.size());
        for (Type.ProductType product : type) {
            boolean isNone = false;
            List<Sort> tuple = new ArrayList<>(product.arity());
            for (int i = 0; i < product.arity(); i++) {
                if (product.get(i).equals(Sig.NONE)) {
                    isNone = true;
                    break;
                }
                tuple.add(getSort(product.get(i)));
            }

            // Ignore "none->none" products - Alloy types have them to signify none
            if (!isNone) {
                tuples.add(tuple);
            }
        }
        return new SortResolvant(new TupleSet<>(tuples, type.arity()));
    }

    @Override
    public Sort getSort(Sig sig) {
        if (sig == Sig.UNIV || sig == Sig.NONE) {
            return null;
        }
        if (sig instanceof Sig.PrimSig) {
            Sort result = sigsToSort.get(sig);
            if (result == null) {
                throw new ErrorFatal("Unknown sig " + sig);
            }
            return result;
        } else {
            // TODO make getSort only take a prim sig
            throw new ErrorFatal("TypeSortPolicy doesn't support subset sigs");
        }
    }

    @Override
    public int getSortScope(Sort sort) {
        if (sort == Sort.Int()) {
            return 1 << scoper.getBitwidth();
        }
        return scoper.sig2scope(sortsToSig.get(sort));
    }

    @Override
    public Expr getCoveringExpr(Sort sort) {
        return sortsToSig.get(sort);
    }

    @Override
    public boolean isSigEntireSort(Sig sig) {
        return true;
    }

    @Override
    public Theory addSortsToTheory(Theory theory) {
        throw new UnsupportedOperationException("TypeSortPolicy is only for preprocessing!");
    }

    @Override
    public List<Sort> getAllSorts() {
        return new ArrayList<>(sigsToSort.values());
    }

}
