package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Assert;
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
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;
import fortress.msfol.Sort;
import fortress.msfol.Theory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * A sort policy that attempts to partition top-level signatures among as many different sorts as possible.
 * Two top-level sigs A and B are assigned to the same sort only if they are used in some way in the
 * model which makes this impossible: e.g. if "forall x: A+B" appears in the model.
 */
final class PartitionSortPolicy extends SortPolicy {

    private final PortusStatistics statistics;

    // For generating unique names.
    private final NameGenerator nameGenerator;

    private final DisjointSets<Sig.PrimSig> sortPartition;

    // Map merged sorts to their merged sorts for converting old sort references to new ones
    private final Map<Sort, Sort> mergedSortMap = new HashMap<>();

    // Cache so we don't generate multiple sorts with the same name
    private final Map<String, Sort> sortNameCache = new HashMap<>();

    private final List<Sig.PrimSig> topLevelSigs;

    private final ModelInfo modelInfo;

    private final ScopeComputer scoper;

    public PartitionSortPolicy(
            PortusStatistics statistics, AlloyProblem problem, ModelInfo modelInfo, ScopeComputer scoper,
            NameGenerator nameGenerator) {
        this(statistics, problem, modelInfo, scoper, nameGenerator, true);
    }

    /**
     * Get a partition sort policy object without merging sorts in instances where the translation requires it.
     * This is useful for seeing the "real" sort resolvant without merges.
     */
    public static PartitionSortPolicy makeWithoutMergingSorts(
            PortusStatistics statistics, AlloyProblem problem, ModelInfo modelInfo,
            ScopeComputer scoper, NameGenerator nameGenerator) {
        return new PartitionSortPolicy(statistics, problem, modelInfo, scoper, nameGenerator, false);
    }

    private PartitionSortPolicy(
            PortusStatistics statistics, AlloyProblem problem, ModelInfo modelInfo, ScopeComputer scoper,
            NameGenerator nameGenerator, boolean shouldMergeSorts) {
        super(problem.getSigs());
        this.statistics = statistics;
        this.modelInfo = modelInfo;
        this.scoper = scoper;
        this.nameGenerator = nameGenerator;

        topLevelSigs = allSigs.stream()
                .filter(sig -> !sig.builtin || sig.equals(Sig.STRING)) // only handle custom top-level sigs and string
                .filter(Sig::isTopLevel)
                .map(sig -> (Sig.PrimSig) sig)
                .collect(Collectors.toList());
        sortPartition = new DisjointSets<>(topLevelSigs);

        if (shouldMergeSorts && !problem.getPortusOptions().enableNoSigHierarchy) {
//            mergeSorts(problem.getFormula());
        }
    }

    private void mergeSorts(Expr formula) {
        // Merge together all sigs' sorts that need to be merged.
        // TODO: We need to pass down the sorts of the ExprElementOf LHS tuple because the logic in DefaultTranslator's
        //   join that determines the sort uses the LHS to short-circuit. This requires major refactoring.
        VisitReturn<Void> merger = new ContextVisitReturn<Void>(new VarMappingContext(), this) {
            @Override
            public Void visit(ExprBinary x) throws Err {
                if (x.op == ExprBinary.Op.PLUSPLUS) {
                    // a ++ b requires all the positions on the RHS to have definite sorts
                    // TODO: technically the first position doesn't but DefaultTranslator requires it
                    mergeSorts(x.right, varMappingContext);
                } else if (x.op == ExprBinary.Op.JOIN) {
                    // a.b requires the middle position to have definite sorts
                    // TODO: this sort of duplicates at least the logic in DefaultTranslator, DRY?
                    mergeSorts(() -> {
                        SortResolvant leftSorts = getMinimalExprSorts(x.left, varMappingContext);
                        SortResolvant rightSorts = getMinimalExprSorts(x.right, varMappingContext);
                        Set<Sort> middle = SetOps.intersection(
                                leftSorts.getSortsInColumn(leftSorts.arity() - 1),
                                rightSorts.getSortsInColumn(0));
                        return SortResolvant.singleColumn(middle);
                    }, varMappingContext);
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
                try {
                    varMappingContext.addLetMappingsFromCall(x);
                    return visitThis(x.fun.getBody());
                } finally {
                    varMappingContext.removeLetMappingsFromCall(x);
                }
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
                } else if (x.op == ExprUnary.Op.CLOSURE || x.op == ExprUnary.Op.RCLOSURE) {
                    // for closure and rclosure, the subexpression's sorts must have arity 2 and
                    // the first and second positions must be the same in all options
                    SortResolvant subSorts = getMinimalExprSorts(x.sub, varMappingContext);
                    if (subSorts.arity() != 2) {
                        throw new ErrorFatal("Argument of ^ or * must have arity 2!");
                    }
                    subSorts.stream().forEach(sorts -> mergeSorts(new HashSet<>(sorts), varMappingContext));
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
            public Void visitQuantifier(ExprQt x, List<Void> argResults, boolean anyArgNone) throws Err {
                // All the quantifier arguments (i.e. e in "all x: e | ...") were already mapped.
                // We can ignore anyArgNone here because we don't care if any ExprVars we meet in the
                // recursion are in the context or not, so it's okay if we meet undefined ExprVars.
                // Technically, it might be more efficient (combine less) to not recurse if anyArgNone, but
                // that threatens correctness if any part of Portus does recurse into it.
                // TODO: Possibility for bug due to conflict between let and none vars?
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
        merger.visitThis(formula);

        // Also make sure every in field declaration "f: e", e has definite sorts
        for (Sig sig : allSigs) {
            for (Sig.Field field : sig.getFields()) {
                mergeSorts(field.decl().expr, new VarMappingContext());
            }
        }

        // In every subset signature, all parents must have the same sort
        for (Sig sig : allSigs) {
            if (sig instanceof Sig.SubsetSig) {
                // Construct a union of the parent sigs and make sure it has one sort
                Expr parentUnion = ((Sig.SubsetSig) sig).parents.stream()
                        .map(parent -> (Expr) parent)
                        .reduce(Expr::plus).orElse(ExprConstant.TRUE);
                mergeSorts(parentUnion, new VarMappingContext());
            }
        }
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

    private Sort getCombinedSort(Sort sort) {
        // the top-level sort is either not in the map or points to itself
        while (mergedSortMap.containsKey(sort) && !mergedSortMap.get(sort).equals(sort)) {
            sort = mergedSortMap.get(sort);
        }
        return sort;
    }

    // Merge sorts until we're able to resolve sorts for expr (or its sorts are none).
    private void mergeSorts(Expr expr, VarMappingContext varMappingContext) {
        mergeSorts(() -> getMinimalExprSorts(expr, varMappingContext), varMappingContext);
    }

    // Merge sorts until we're able to resolve sorts for toMerge (or its sorts are none).
    private void mergeSorts(Supplier<SortResolvant> toMerge, VarMappingContext varMappingContext) {
        // TODO: is the iteration even necessary here?
        boolean allDefinite = false;
        while (!allDefinite) {
            allDefinite = true;
            SortResolvant sortResolvant = toMerge.get();
            if (!sortResolvant.isDefinite() && !sortResolvant.isNone()) {
                allDefinite = false;
                // Merge the sorts in each column to merge everything into one
                for (int column = 0; column < sortResolvant.arity(); column++) {
                    mergeSorts(sortResolvant.getSortsInColumn(column), varMappingContext);
                }
            }
        }
    }

    private void mergeSorts(Set<Sort> sorts, VarMappingContext varMappingContext) {
        if (sorts.size() == 1) {
            // nothing to merge
            return;
        }

        Sig.PrimSig first = null;
        for (Sort sort : sorts) {
            // We can't merge built-in sorts
            if (sort.isBuiltin()) {
                // TODO: this error message is rather cryptic
                throw new ErrorNoPortusSupport(
                        "Incompatible sorts: cannot merge Int or other built-in sorts!");
            }

            // Find the sort this was merged into to allow merging old references to sorts
            Sort combinedSort = getCombinedSort(sort);
            Sig.PrimSig sig = getAnySigFromSort(combinedSort);
            if (sig == null) {
                throw new ErrorFatal("Unknown sort: " + sort);
            }
            Sig.PrimSig topLevel = getTopLevel(sig);
            if (first == null) {
                first = topLevel;
            } else {
                if (!sortPartition.areSameSet(first, topLevel)) {
                    statistics.sortMerges.increment();
                }
                sortPartition.unite(first, topLevel);
            }
        }

        // Replace all the sorts with the new sort in the context to avoid inconsistent history
        if (first != null) {
            Sort combinedSort = getSort(first);
            for (Sort sort : sorts) {
                varMappingContext.replaceSort(sort, combinedSort);
                mergedSortMap.put(sort, combinedSort);
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
        Sort sort = Sort.mkSortConst(nameGenerator.freshName(name));
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
        if (Sort.Int().equals(sort)) {
            return 1 << scoper.getBitwidth();
        } else if (sort.isBuiltin()) {
            throw new ErrorFatal("Cannot get scope for non-int builtin sort: " + sort);
        }

        Sig.PrimSig someSig = getAnySigFromSort(sort);
        Set<Sig.PrimSig> allSigs = sortPartition.getSet(getTopLevel(someSig));

        // Just the sum of all the top-level sigs in the sort
        int scope = 0;
        for (Sig.PrimSig sig : allSigs) {
            if (sig == Sig.STRING) {
                scope += modelInfo.numStringConstants(); // sig2scope returns incorrect results for String
            } else {
                scope += scoper.sig2scope(sig);
            }
        }

        // Don't set a scope of 0, Fortress doesn't support that.
        // This is okay because MembershipPredicateOptTranslator doesn't optimize out the membership predicate
        // when the sort scope would be 0, so correctness isn't impacted.
        return Math.max(scope, 1);
    }

    @Override
    public Expr getCoveringExpr(Sort sort) {
        if (Sort.Int().equals(sort)) {
            return Sig.SIGINT;
        } else if (sort.isBuiltin()) {
            throw new ErrorFatal("Cannot get covering expr for non-int builtin sort: " + sort);
        }

        // Add all the top level sigs that are part of it together
        // TODO if we go to sorts for subclasses and for "remainder sorts" (Edwards, Jackson, Torlak) this won't work
        return topLevelSigs.stream()
                .filter(sig -> sort.equals(getSort(sig)))
                .map(sig -> (Expr) sig)
                .reduce(Expr::plus)
                .orElse(ExprConstant.EMPTYNESS);
    }

    @Override
    public boolean isSigEntireSort(Sig sig) {
        // Special cases: builtin sigs
        if (sig == Sig.SIGINT) {
            return true; // SIGINT is all of Sort.Int
        } else if (sig.builtin && sig != Sig.STRING) {
            // None of the others (although technically SEQIDX might be? and univ is tricky)
            // TODO: handle SEQIDX better here
            return false;
        }

        if (!(sig instanceof Sig.PrimSig)) {
            // Subset sigs by definition don't take the entire sort
            return false;
        }

        if (!sig.isTopLevel()) {
            // TODO: Should we bother trying to tell if a subsig is the whole sort?
            return false;
        }

        Sig.PrimSig primSig = (Sig.PrimSig) sig;

        // Top-level sigs with non-exact scope and subsigs can't use the Fortress non-exact scope,
        // because the scope axiom strategies need the parent sort to be exact. So they have to use
        // exact scope Fortress sorts and so they can't be the entire sort.
        // TODO: This is dependent on the scope axiom strategy but cardinality + constants need it so it's probably fine
        if (!scoper.isExact(primSig) && !primSig.children().isEmpty()) {
            return false;
        }

        return sortPartition.getSet(primSig).size() == 1;
    }

    @Override
    public Theory addSortsToTheory(Theory theory) {
        for (Sort sort : getAllSorts()) {
            if (!Objects.equals(sort, Sort.Int())) { // only the int sort shouldn't be added
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
