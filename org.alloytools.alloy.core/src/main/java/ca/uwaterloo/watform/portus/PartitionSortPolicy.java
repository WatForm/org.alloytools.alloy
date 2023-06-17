package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Theory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * A sort policy that attempts to partition top-level signatures among as many different sorts as possible.
 * Two top-level sigs A and B are assigned to the same sort only if they are used in some way in the
 * model which makes this impossible: e.g. if "forall x: A+B" appears in the model.
 */
final class PartitionSortPolicy extends SortPolicy {

    private final DisjointSets<Sig.PrimSig> sortPartition;

    // Cache so we don't generate multiple sorts with the same name
    private final Map<String, Sort> sortNameCache = new HashMap<>();

    private final List<Sig.PrimSig> topLevelSigs;

    private final ScopeComputer scoper;
//    private final Map<Sig, Sort> sigsToSorts = new HashMap<>();
//    private final List<Sort> allSorts = new ArrayList<>();
//    private final Map<Sort, Scope> sortsToScopes = new HashMap<>();

    public PartitionSortPolicy(Iterable<Sig> allSigs, Command command, ScopeComputer scoper) {
        super(allSigs);
        this.scoper = scoper;

        topLevelSigs = StreamSupport.stream(allSigs.spliterator(), false)
                .filter(sig -> !sig.builtin) // only handle custom top-level sigs
                .filter(Sig::isTopLevel)
                .map(sig -> (Sig.PrimSig) sig)
                .collect(Collectors.toList());
        sortPartition = new DisjointSets<>(topLevelSigs);

        // Merge together all sigs' sorts that need to be merged.
        VisitReturn<Void> merger = new ContextVisitReturn<Void>(new VarMappingContext(), this) {
            @Override
            public Void visit(ExprBinary x) throws Err {
                switch (x.op) {
                    case PLUSPLUS:
                        // a ++ b requires all the positions to have matching sorts
                        // TODO: technically the first position doesn't but DefaultTranslator requires it
                        mergeSorts(x, varMappingContext);
                        break;
//                    case IN:
//                    case NOT_IN:
//                        // a in b requires left and right to have matching sorts, but right could be univ
//                        uniteTypeSigs(mergeTypesExcludingUnivOnRight(x.left.type(), x.right.type()));
//                        break;
//                    case EQUALS:
//                    case NOT_EQUALS:
//                        // a = b requires both positions to have matching sorts
//                        // TODO: we could probably short circuit instead (see DefaultTranslator)
//                        uniteTypeSigs(x.left.type().merge(x.right.type()));
//                        break;
//                    case JOIN:
//                        // We require the middle position to have matching sorts
//                        // Note this holds even when the join is optimized
//                        for (Type.ProductType productTypeLeft : x.left.type()) {
//                            Sig sigLeft = getTopLevel(productTypeLeft.get(productTypeLeft.arity() - 1));
//                            for (Type.ProductType productTypeRight : x.right.type()) {
//                                Sig sigRight = getTopLevel(productTypeRight.get(0));
//                                sortPartition.unite(sigLeft, sigRight);
//                            }
//                        }
//                        break;
                }

                visitThis(x.left);
                return visitThis(x.right);
            }

            @Override
            public Void visit(ExprList x) throws Err {
                x.args.forEach(this::visitThis);
                return null;
            }

            @Override
            public Void visit(ExprCall x) throws Err {
                x.args.forEach(this::visitThis);
                return visitThis(x.fun.getBody());
            }

            @Override
            public Void visit(ExprConstant x) throws Err {
                // nothing of interest
                return null;
            }

            @Override
            public Void visit(ExprITE x) throws Err {
                visitThis(x.cond);
                visitThis(x.left);
                return visitThis(x.right);
            }

            @Override
            public Void visit(ExprUnary x) throws Err {
                if (x.op == ExprUnary.Op.SOME
                        || x.op == ExprUnary.Op.NO
                        || x.op == ExprUnary.Op.LONE
                        || x.op == ExprUnary.Op.ONE) {
                    // the expression in a quantification like "some e" must have definite sorts
                    mergeSorts(x.sub, varMappingContext);
                }
                return visitThis(x.sub);
            }

            @Override
            public Void visit(Sig x) throws Err {
                // nothing of interest
                return null;
            }

            @Override
            public Void visit(Sig.Field x) throws Err {
                // nothing of interest
                return null;
            }

            @Override
            public Void visit(ExprElementOf x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public Void visitLet(ExprLet x) throws Err {
                // context taken care of by superclass
                return visitThis(x.sub);
            }

            @Override
            public Void visitVar(ExprVar x) throws Err {
                // recursing into lets taken care of by superclass
                return null;
            }

            @Override
            public Void visitQuantifier(ExprQt x, List<Void> argResults) throws Err {
                // All the quantifier arguments (i.e. e in "all x: e | ...") were already mapped
                return visitThis(x.sub);
            }

            @Override
            public Void visitQuantifierArg(Expr arg) throws Err {
                // In e.g. "all x: e | ...", e must have definite sorts
                mergeSorts(arg, varMappingContext);
                return visitThis(arg);
            }

            @Override
            public Void visit(Func x) throws Err {
                throw new ErrorFatal("Cannot visit Func!");
            }

            @Override
            public Void visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot visit Assert!");
            }

            @Override
            public Void visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot visit Macro!");
            }
        };
        merger.visitThis(command.formula);

        // Also make sure every in field declaration "f: e", e has definite sorts
        for (Sig sig : allSigs) {
            for (Sig.Field field : sig.getFields()) {
                mergeSorts(field.decl().expr, new VarMappingContext());
            }
        }

        // In every subset signature, all parents must have the same sort
        // Luckily, the type of the subset signature is the union of the parents' top level signatures
        for (Sig sig : allSigs) {
            if (sig instanceof Sig.SubsetSig) {
                mergeSorts(sig, new VarMappingContext());
            }
        }

        // Now that we've figured out what sigs need to be in the same sorts, generate the sorts
//        List<List<Sig>> partition = sortPartition.getPartition();
//        for (List<Sig> sigsInSameSort : partition) {
//            String name = getSortNameFromSigs(sigsInSameSort);
//            Sort sort = Sort.mkSortConst(name);
//
//            int sortScope = 0;
//            for (Sig sig : sigsInSameSort) {
//                sigsToSorts.put(sig, sort);
//                int scope = scoper.sig2scope(sig);
//                if (scope <= 0) {
//                    throw new ErrorFatal("Sig " + sig + " should be a user-defined sig with a scope, not " + scope);
//                }
//                sortScope += scope;
//            }
//            allSorts.add(sort);
//            // TODO: If this is the only top-level sort, we can save on a scope axiom using non-exact scopes here!
//            sortsToScopes.put(sort, ExactScope.apply(sortScope));
//        }

        // Special cases for int
//        allSorts.add(Sort.Int());
//        sortsToScopes.put(Sort.Int(), ExactScope.apply(1 << scoper.getBitwidth())); // 2^bitwidth, # of ints
//        sigsToSorts.put(Sig.SIGINT, Sort.Int());
//        sigsToSorts.put(Sig.SEQIDX, Sort.Int());
    }

    private int getArity(Type type) {
        // All of the product types should be the same arity - we don't handle anything else
        int arity = type.arity();
        if (arity <= 0) { // either incompatible arities or nothing at all
            throw new ErrorFatal("Portus cannot handle types with incompatible/no arities: " + type);
        }
        return arity;
    }

    private Sig.PrimSig getTopLevel(Sig.PrimSig sig) {
        if (sig == Sig.UNIV || sig == Sig.NONE) {
            throw new ErrorFatal("Cannot assign univ or none to a partition!");
        }

        while (!sig.isTopLevel()) {
            sig = sig.parent;
        }
        return sig;
    }

//    // Merge all the corresponding sigs in the product types in the partition
//    private void uniteTypeSigs(Type type) {
//        for (int idx = 0; idx < getArity(type); idx++) {
//            Sig.PrimSig first = null;
//            for (Type.ProductType productType : type) {
//                Sig.PrimSig sig = productType.get(idx);
//                if (sig == Sig.NONE) {
//                    // Ignore Sig.NONE: never unite with anything (it always short-circuits)
//                    continue;
//                }
//                Sig.PrimSig topLevel = getTopLevel(sig);
//                if (first == null) {
//                    first = topLevel;
//                } else {
//                    sortPartition.unite(first, topLevel);
//                }
//            }
//        }
//    }

    // Merge sorts until we're able to resolve sorts for expr.
    private void mergeSorts(Expr expr, VarMappingContext varMappingContext) {
        while (true) {
            try {
                getMinimalExprSortsOrThrow(expr, varMappingContext);
                return;
            } catch (IncompatibleSortsException e) {
                // We have a list of sorts we have to merge
                mergeSorts(e.incompatibleSorts, varMappingContext);
            }
        }
    }

    private void mergeSorts(List<Sort> sorts, VarMappingContext varMappingContext) {
        Sig.PrimSig first = null;
        for (Sort sort : sorts) {
            // We can't merge built-in sorts
            if (sort.isBuiltin()) {
                // TODO: this error message is rather cryptic
                throw new ErrorFatal("Incompatible sorts: cannot merge Int or other built-in sorts!");
            }

            Sig.PrimSig sig = getAnySigFromSort(sort);
            if (sig == null) {
                throw new ErrorFatal("Unknown sort: " + sort);
            }
            Sig.PrimSig topLevel = getTopLevel(sig);
            if (first == null) {
                first = topLevel;
            } else {
                sortPartition.unite(first, topLevel);
            }
        }

        // Replace all the sorts with the new sort in the context to avoid inconsistent history
        if (first != null) {
            Sort combinedSort = getSort(first);
            for (Sort sort : sorts) {
                varMappingContext.replaceSort(sort, combinedSort);
            }
        }
    }

    /** Generate a not-useless name for a sort containing the list of sigs. */
    private String getSortNameFromSigs(Set<Sig.PrimSig> sigs) {
        if (sigs.isEmpty()) {
            throw new ErrorFatal("Cannot generate a sort name for zero sigs!");
        }

        // Just choose the first alphabetically
        return "Sort_" + sigs.stream()
                .map(sig -> sig.label)
                .sorted()
                .findFirst().get();
    }

    /** Create a sort with the given name, or retrieve one with the same name from the cache. */
    private Sort makeSort(String name) {
        if (sortNameCache.containsKey(name)) {
            return sortNameCache.get(name);
        }
        Sort sort = Sort.mkSortConst(name);
        sortNameCache.put(name, sort);
        return sort;
    }

    @Override
    public Sort getSort(Sig sig) {
        // Exceptions for built-in signatures
        if (sig == Sig.SIGINT || sig == Sig.SEQIDX) {
            return Sort.Int();
        }
        if (sig == Sig.UNIV || sig == Sig.NONE) {
            // We can't assign a sort to univ or none
            return null;
        }
        if (sig == Sig.STRING) {
            // String can't be assigned a sort for now - TODO strings
            return null;
        }

        if (sig instanceof Sig.PrimSig) {
            Sig.PrimSig topLevelSig = getTopLevel((Sig.PrimSig) sig);
            Set<Sig.PrimSig> sigsInSort = sortPartition.getSet(topLevelSig);
            return makeSort(getSortNameFromSigs(sigsInSort));
        } else {
            // it's a subset signature - all parents have same sort, so pick one
            while (sig instanceof Sig.SubsetSig) {
                sig = ((Sig.SubsetSig) sig).parents.get(0);
            }
            return getSort(sig);
        }
    }

    @Override
    public int getSortScope(Sort sort) {
        // Special cases for builtin sorts
        if (sort == Sort.Int()) {
            return 1 << scoper.getBitwidth();
        } else if (sort.isBuiltin()) {
            throw new ErrorFatal("Cannot get scope for non-int builtin sort: " + sort);
        }

        Sig.PrimSig someSig = getAnySigFromSort(sort);
        Set<Sig.PrimSig> allSigs = sortPartition.getSet(someSig);

        // Just the sum of all the top-level sigs in the sort
        int scope = 0;
        for (Sig.PrimSig sig : allSigs) {
            scope += scoper.sig2scope(sig);
        }
        return scope;
    }

    @Override
    public boolean isSigEntireSort(Sig sig) {
        // Special cases: builtin sigs
        if (sig == Sig.SIGINT) {
            return true; // SIGINT is all of Sort.Int
        } else if (sig.builtin) {
            // None of the others (although technically SEQIDX might be? and univ is tricky)
            // TODO: handle SEQIDX better here
            return false;
        }

        if (!(sig instanceof Sig.PrimSig)) {
            // Subset sigs by definition don't take the entire sort
            return false;
        }
        Sig.PrimSig primSig = (Sig.PrimSig) sig;
        Sig.PrimSig topLevel = getTopLevel(primSig);

        // Top-level sigs with non-exact scope and subsigs can't use the Fortress non-exact scope,
        // because the scope axiom strategies need the parent sort to be exact. So they have to use
        // exact scope Fortress sorts and so they can't be the entire sort.
        // TODO: This is dependent on the scope axiom strategy but cardinality + constants need it so it's probably fine
        if (!scoper.isExact(topLevel) && !topLevel.children().isEmpty()) {
            return false;
        }

        return sortPartition.getSet(topLevel).size() == 1;
    }

    @Override
    public Theory addSortsToTheory(Theory theory) {
        for (Sort sort : getAllSorts()) {
            if (sort != Sort.Int()) { // only the int sort shouldn't be added
                theory = theory.withSort(sort);
            }
        }
        return theory;
    }

    @Override
    public List<Sort> getAllSorts() {
        // Naively get the sorts of every sig
        // This has real poor time complexity, but that's okay
        Set<Sort> allSorts = new HashSet<>();
        for (Sig.PrimSig sig : topLevelSigs) {
            allSorts.add(getSort(sig));
        }
        allSorts.add(Sort.Int());
        return new ArrayList<>(allSorts);
    }

}
