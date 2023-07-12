package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.Sort;

import java.util.Set;

/**
 * An ScopeExpansionMarker is something that, given an expression, can determine a set of sorts
 * whose scopes will be expanded over during translation.
 */
interface ScopeExpansionMarker {

    /**
     * Given an expression, determine a list of sorts that will be expanded over.
     * Note: this is passed into NaturalRecursion.accumulate, so it does *not* need to recurse
     * into subexpressions.
     */
    Set<Sort> determineExpandedSorts(Expr expr, VarMappingContext varMappingContext);

}
