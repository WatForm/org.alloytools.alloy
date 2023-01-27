package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.VisitReturn;

/**
 * A {@link VisitReturn} that visits custom Portus Expr nodes.
 * Also contains some conveniences used in translation.
 */
public abstract class FortressVisitReturn<T> extends VisitReturn<T> {

    /** Visits an ExprElementOf custom node. */
    public abstract T visit(ExprElementOf x) throws Err;

    /** Convenience: delegate visiting a sig to PrimSig or SubsetSig overloads. */
    @Override
    public T visit(Sig sig) throws Err {
        if (sig instanceof Sig.PrimSig) {
            return visit((Sig.PrimSig) sig);
        } else {
            return visit((Sig.SubsetSig) sig);
        }
    }

    // These aren't abstract in case a subclass decides to overload visit(Sig) instead.

    /** Visits a PrimSig. */
    public T visit(Sig.PrimSig x) throws Err {
        return null;
    }

    /** Visits a SubsetSig */
    public T visit(Sig.SubsetSig x) throws Err {
        return null;
    }

}
