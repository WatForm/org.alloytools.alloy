package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * An optimization which translates top-level signatures without their membership predicate when it is
 * possible to do so. It uses a pass before the main translation pass to determine the sorts we can
 * optimize out membership predicates from (relying on the Fortress sort).
 */
final class MembershipPredicateOptTranslator extends AbstractTranslator implements Evaluator {

    private final SortPolicy sortPolicy;
    private final SigAxioms sigAxioms;

    private final Set<Sort> inapplicableSorts = new HashSet<>();

    /**
     * If true, we will never rely on Fortress's non-exact scope feature by always generating a membership predicate
     * for sigs with non-exact scopes.
     */
    private final boolean noFortressNonExactScopes;

    public MembershipPredicateOptTranslator(Translator topLevel, SortPolicy sortPolicy, SigAxioms sigAxioms,
                                            boolean noFortressNonExactScopes) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
        this.sigAxioms = sigAxioms;
        this.noFortressNonExactScopes = noFortressNonExactScopes;
    }

    @Override
    public String name() {
        return "Membership Predicate Optimization";
    }

    /**
     * Return a Pass that must be run before the main translation pass which populates the list of sorts
     * this optimization is inapplicable to. The list of scope expansion markers will be consulted for every
     * expression in the AST to determine which sorts' scopes are expanded over in that expression.
     */
    public Pass getApplicabilityDeterminingPass(List<ScopeExpansionMarker> scopeExpansionMarkers) {
        return (problem, scoper, context) -> {
            for (Sig sig : problem.getSigs()) {
                determineApplicabilityFromSig(sig, scoper);
            }

            // Perform a pass over the command and determine all inapplicable sorts.
            // If we ever expand over a sort, we can't optimize it here.
            inapplicableSorts.addAll(NaturalRecursion.accumulate(
                    (expr, varMappingContext) -> scopeExpansionMarkers.stream()
                        .map(marker -> marker.determineExpandedSorts(expr, varMappingContext))
                        .reduce(new HashSet<>(), SetOps::union),
                    problem.getFormula(), sortPolicy, new VarMappingContext()));
        };
    }

    private void determineApplicabilityFromSig(Sig sig, ScopeComputer scoper) {
        if (isSigIneligible(sig)) {
            // Don't handle builtin sigs or non-toplevel sigs
            return;
        }

        Sig.PrimSig primSig = (Sig.PrimSig) sig;
        Sort sort = sortPolicy.getSort(primSig);

        if (primSig.isTopLevel() && !sortPolicy.isSigEntireSort(primSig)) {
            // The opt is only applicable to sorts that are only one top-level sig
            inapplicableSorts.add(sort);
            return;
        }

        // Top-level sigs with non-exact scope require membership predicates (i.e. they can't use Fortress
        // non-exact scope) because the scope axiom strategies need the parent sort to be exact.
        // So they have to use exact scope Fortress sorts and so we can't apply the membership predicate opt.
        // TODO: This is dependent on the scope axiom strategy but cardinality + constants need it so it's probably fine
        // TODO: but if we change the cardinality implementation, it might not need it...
        // Also, if we explicitly disable Fortress-level non-exact scopes, don't rely on them.
        if (!scoper.isExact(primSig) && (noFortressNonExactScopes || !primSig.children().isEmpty())) {
            inapplicableSorts.add(sort);
            return;
        }

        // Patch: Alloy allows sig scopes to be set to 0, but Fortress sorts don't support scope 0.
        // Avoid setting a scope of 0 on Fortress sorts by disallowing sigs of scope 0.
        if (scoper.sig2scope(primSig) == 0) {
            inapplicableSorts.add(sort);
        }
    }

    private boolean isSigIneligible(Sig sig) {
        return sig.builtin || !(sig instanceof Sig.PrimSig) || !sig.isTopLevel();
    }

    private boolean isInapplicableToSig(Sig sig) {
        if (isSigIneligible(sig)) {
            return true;
        }
        Sort sigSort = sortPolicy.getSort(sig);
        return inapplicableSorts.contains(sigSort);
    }

    /** Generate optimized axioms for sigs we can optimize. */
    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (isInapplicableToSig(sig)) {
            return null;
        }

        // It's applicable - the sig is the entire sort, no membership predicate.
        Sig.PrimSig primSig = (Sig.PrimSig) sig;

        // Translate all children recursively as required
        for (Sig.PrimSig child : primSig.children()) {
            recursivelyTranslate(child, context);
        }

        // Add only the axioms specifying the relations between the sig and its children.
        // No scope axiom - we'll use the Fortress scopes.
        sigAxioms.addPrimSigChildrenAxioms(primSig, context);

        // Also handle one, lone, some sigs
        sigAxioms.addSigMultiplicityAxiom(sig, context);

        return Term.mkTop();
    }

    /** Translate "x \in sig", where sig is optimized here. */
    @Override
    public Term translate(AnnotatedTerm term, Sig sig, TranslationContext context) {
        if (isInapplicableToSig(sig)) {
            return null;
        }

        // The sig is the entire sort, so a term is in the sig iff its sort matches the sig's sort.
        Sort sigSort = sortPolicy.getSort(sig);
        boolean inSort = Objects.equals(term.getSort(), sigSort);
        return inSort ? Term.mkTop() : Term.mkBottom();
    }

    @Override
    public ValueTupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        if (!(expr instanceof Sig) || isInapplicableToSig((Sig) expr)) {
            return null;
        }
        Sig.PrimSig sig = (Sig.PrimSig) expr;

        // The sig is the entire sort, so the results are the entire sort
        return ValueTupleSet.atoms(solution.getSortAtoms(sortPolicy.getSort(sig)));
    }

}
