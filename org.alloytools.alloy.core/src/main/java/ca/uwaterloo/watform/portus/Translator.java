package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.Term;

/**
 * A translator is something that can try to translate an Alloy expression to a Fortress Term.
 */
@FunctionalInterface
interface Translator {

    /**
     * Translate an Alloy expression to a Fortress term, or return null if we can't.
     * @param expr The Alloy expression to translate.
     * @param context The context for the translation. If this method returns null, it
     *                must not mutate the context. Otherwise, it may mutate it.
     * @return The Fortress term corresponding to the Alloy expression, or null if
     *         this expression is not supported.
     */
    Term translate(Expr expr, TranslationContext context);

    /**
     * The name of the translator, for display purposes.
     */
    default String name() {
        return "(anonymous)";
    }

}
