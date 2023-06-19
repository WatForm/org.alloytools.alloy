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

    public OneSigOptTranslator(Translator topLevel, SortPolicy sortPolicy) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
    }

    /** Process one sigs and add axioms. */
    @Override
    public Term translate(Sig sig, TranslationContext context) {
        // Don't bother trying to deal with one subset sigs, they aren't common
        if (sig.isOne == null || !(sig instanceof Sig.PrimSig)) return null;

        // Don't add all the axioms or create a predicate, just use the range axiom
        context.rangeAssigner.addRangeAxiom(sig, topLevelTranslator, sortPolicy, context);
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
    public TupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        DomainElement domainElement = castToDomainElement(expr, context);
        if (domainElement == null) return null;

        return TupleSet.singleton(solution.evaluateTerm(domainElement));
    }

    private DomainElement castToDomainElement(Expr expr, TranslationContext context) {
        if (!(expr instanceof Sig)) return null;
        Sig sig = (Sig) expr;
        if (sig.isOne == null || !(sig instanceof Sig.PrimSig)) return null;

        return PortusUtil.getOneSigDomainElement((Sig.PrimSig) sig, sortPolicy, context);
    }

}
