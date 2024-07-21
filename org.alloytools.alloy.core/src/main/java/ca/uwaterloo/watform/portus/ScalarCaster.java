package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;

/**
 * A scalar caster is something that can try to cast an Alloy expression to a scalar Fortress term.
 */
@FunctionalInterface
interface ScalarCaster {

    /**
     * Attempt to cast expr to a scalar Fortress term.
     * Return a pair of the scalar term and a guard term, or null if this caster can't cast expr to a scalar.
     * Use of the scalar term must be conditioned on the guard (it could be a domain check, for example); the guard
     * evaluates to false iff the expr evaluates to the empty set. The guard will be Top if it is not necessary.
     */
    Pair<AnnotatedTerm, AnnotatedTerm> castToScalar(Expr expr, TranslationContext context);

    /**
     * The name of the scalar caster, for display purposes.
     */
    default String name() {
        return "(anonymous)";
    }

}
