package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;

/**
 * Something that can execute a command: transforming a command to an {@link A4Solution}.
 *
 * @since Added by Portus
 */
public interface CommandRunner {

    /**
     * Execute a command based on the given options and return the resulting solution.
     *
     * @param rep - send diagnostic messages to this if nonnull
     * @param sigs - a complete list of sigs in the model
     * @param cmd - the command to execute
     * @param opts - options guiding the execution of the command
     * @return an {@link A4Solution} if the solver finished solving and the model was found to be
     *         satisfiable or unsatisfiable, or null if the solver does not give a result
     *         (e.g. "save to file").
     */
    A4Solution executeCommand(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opts);

}
