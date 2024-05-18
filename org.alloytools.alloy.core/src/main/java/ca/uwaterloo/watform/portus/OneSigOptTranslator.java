package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.DomainElement;
import fortress.msfol.Term;

/**
 * A translator that optimizes one sigs as constants. Primarily, this ensures they're treated as scalars
 * and removes unnecessary axioms.
 *
 * Requires SimpleScalarOptTranslator to translate [[x \in OneSig]].
 * TODO: Duplicate some functionality so as not to require SimpleScalarOptTranslator?
 */
class OneSigOptTranslator extends AbstractTranslator implements ScalarCaster, Evaluator {

    private final SortPolicy sortPolicy;
    private final SigAxioms sigAxioms;

    public OneSigOptTranslator(Translator topLevel, SortPolicy sortPolicy, SigAxioms sigAxioms) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
        this.sigAxioms = sigAxioms;
    }

    @Override
    public String name() {
        return "One Sig Optimization";
    }

    private boolean isChildOfOrderedSig(Sig.PrimSig sig, TranslationContext context) {
        return context.isSigOrdered(sig) || (!sig.isTopLevel() && isChildOfOrderedSig(sig.parent, context));
    }

    private boolean isInapplicable(Sig sig, TranslationContext context) {
        // Don't bother trying to deal with one subset sigs, they aren't common.
        // Also, we can't optimize children of ordered sigs because the assignment of one sigs to
        // particular domain elements might conflict with the hardcoded order that the ordering
        // module imposes. So just disable it in that case.
        return sig.isOne == null
                || !(sig instanceof Sig.PrimSig)
                || isChildOfOrderedSig((Sig.PrimSig) sig, context);
    }

    /** Process one sigs and add axioms. */
    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (isInapplicable(sig, context)) return null;
        Sig.PrimSig primSig = (Sig.PrimSig) sig;

        // Don't add all the axioms or create a predicate, just use the range axiom
        context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, context);

        // Translate all the children (yes, one sigs can have children)
        // But don't bother trying to optimize the sig axioms, because this isn't common
        for (Sig.PrimSig child : primSig.children()) {
            recursivelyTranslate(child, context);
        }
        sigAxioms.addPrimSigChildrenAxioms(primSig, context);

        return Term.mkTop();
    }

    /** Cast an instance of a one sig to a scalar: its domain element. */
    @Override
    public Pair<AnnotatedTerm, Term> castToScalar(Expr expr, TranslationContext context) {
        DomainElement domainElement = castToDomainElement(expr, context);
        if (domainElement == null) return null;

        // No guard is needed
        return new Pair<>(new AnnotatedTerm(domainElement, domainElement.sort()), Term.mkTop());
    }

    /** Evaluate an instance of a one sig as the value corresponding to its domain element. */
    @Override
    public ValueTupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        DomainElement domainElement = castToDomainElement(expr, context);
        if (domainElement == null) return null;

        return ValueTupleSet.singleton(solution.evaluateTerm(domainElement));
    }

    private DomainElement castToDomainElement(Expr expr, TranslationContext context) {
        if (!(expr instanceof Sig)) return null;
        Sig sig = (Sig) expr;
        if (isInapplicable(sig, context)) return null;

        return PortusUtil.getOneSigDomainElement((Sig.PrimSig) sig, sortPolicy, context);
    }

}
