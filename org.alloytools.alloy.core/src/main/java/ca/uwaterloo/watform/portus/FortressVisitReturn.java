package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.VisitReturn;

/**
 * A {@link VisitReturn} that visits custom Portus Expr nodes.
 * Also contains some conveniences used in translation.
 */
public abstract class FortressVisitReturn<T> extends VisitReturn<T> {

    /** Visits an ExprElementOf custom node. */
    public abstract T visit(ExprElementOf x) throws Err;

}
