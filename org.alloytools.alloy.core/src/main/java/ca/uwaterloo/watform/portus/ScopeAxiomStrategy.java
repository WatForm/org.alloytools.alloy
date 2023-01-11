package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.Term;

/**
 * An abstraction over techniques for creating the axioms limiting the scopes of sigs.
 * Methods are expected to return the axioms rather than adding them to the context.
 * Use the recursiveTranslator to make recursive translations. TODO would it be better to add this to the context?
 */
interface ScopeAxiomStrategy {

    /** Create an axiom expressing that the scope of sig is exactly scope. */
    Term makeExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context);

    /** Create an axiom expressing that the scope of sig is at most scope. */
    Term makeNonExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context);

}
