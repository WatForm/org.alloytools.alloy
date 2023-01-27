package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.io.Serializable;

/**
 * All the Fortress-specific options configurable by the user. Immutable.
 */
public final class FortressOptions implements Serializable {

    /**
     * A {@link SatSolver} that uses Fortress as its {@link CommandRunner}.
     * Actually an SMT solver, not a SAT solver.
     */
    public static final class FortressSmtSolver extends SatSolver implements Serializable {

        /** Ensure we can serialize correctly. */
        private static final long serialVersionUID = 0L;

        // TODO: I'd prefer this to be private...
        public FortressSmtSolver(String id, String toString) {
            // No Fortress solver is an external command and we always want to add to the solver list,
            // so pass null for the external command and options and true for whether to add.
            super(id, toString, null, null, true);
        }

        @Override
        public CommandRunner commandRunner() {
            return new TranslateAlloyToFortress();
        }

    }

    /** Ensure we can serialize correctly. */
    private static final long serialVersionUID = 0L;

    /** Which sort policy should we use to translate? */
    public SortPolicy getSortPolicy(Iterable<Sig> sigs, ScopeComputer scoper) {
        // For now, always use the univ sort policy
        return new UnivSortPolicy(sigs, scoper);
    }

    // TODO: some options, used to determine optimizations

}
