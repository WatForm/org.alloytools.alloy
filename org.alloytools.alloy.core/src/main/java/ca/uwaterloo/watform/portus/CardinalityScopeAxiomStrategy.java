package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;

/**
 * A scope axiom strategy that uses cardinality to express scopes.
 * NOTE: Using this requires that the bitwidth is large enough to express the largest sig scope.
 * Use the '-b' option in the CLI to automatically bump up the bitwidth to be large enough.
 */
final class CardinalityScopeAxiomStrategy implements ScopeAxiomStrategy {

    @Override
    public Term makeExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        // "#sig = scope"
        checkSufficientBitwidth(sig, context);
        return Term.mkEq(
                recursiveTranslator.translate(sig.cardinality(), context),
                IntegerLiteral.apply(scope));
    }

    @Override
    public Term makeNonExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        // "#sig <= scope"
        checkSufficientBitwidth(sig, context);
        return Term.mkLE(
                recursiveTranslator.translate(sig.cardinality(), context),
                IntegerLiteral.apply(scope));
    }

    private void checkSufficientBitwidth(Sig sig, TranslationContext context) {
        // To use this technique, we require the max size of the sig's sort to be representable as an integer.
        // (This is always at least the scope we're trying to check, so we don't check that explicitly.)
        // TODO: if Fortress's integer implementation changes, this might be unnecessary
        Sort sort = context.sortPolicy.getSort(sig);
        if (sort == null) {
            throw new ErrorFatal("Can only generate a cardinality scope axiom for sigs with defined sorts!");
        }
        int sortScope = context.sortPolicy.getSortScope(sort);
        if (sortScope > Util.max(context.getBitwidth())) {
            throw new ErrorFatal("Cardinality-based scope axioms require a bitwidth of at least "
                    + requiredBitwidthForScope(sortScope)
                    + " (to represent the '" + sort.name() + "' Fortress sort of max scope " + sortScope + ") "
                    + "but bitwidth is " + context.getBitwidth());
        }
    }

    private int requiredBitwidthForScope(int scope) {
        int bitwidth = 0;
        while (scope > Util.max(bitwidth)) {
            bitwidth++;
        }
        return bitwidth;
    }

}
