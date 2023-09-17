package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * Something that can process an Alloy command in a way we might want to invoke from the CLI.
 * Implementations will be run once for every command in an Alloy file.
 */
interface CommandProcessor {

    /** Process the given command with the given list of sigs. Return whether it was successful. */
    boolean process(Module world, Command command, A4Options options);

    // What should this processor be called in output?
    String displayName();

}
