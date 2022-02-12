package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.Theory;

/**
 * A translator is something that can try to translate an Alloy expression
 * to a Fortress theory.
 */
@FunctionalInterface
interface Translator {

    /**
     * Translate `expr` to a Fortress theory using `base` as the base Theory, or
     * return null if we can't handle the given expression.
     * @param expr The Alloy expression to translate.
     * @param base A base Fortress theory to use. The return value should be derived
     *             from this theory if it is not null.
     * @return The base Fortress theory augmented with the translation of the expression,
     *         or null if we can't build a theory from the expression.
     */
    Theory translate(Expr expr, Theory base);

}
