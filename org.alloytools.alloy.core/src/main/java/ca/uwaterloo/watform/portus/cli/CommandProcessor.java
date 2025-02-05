package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.AlloyProblem;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * Something that can process an Alloy problem in a way we might want to invoke from the CLI.
 * Implementations will be run once for every command in an Alloy file.
 */
interface CommandProcessor {

    /** Process the given problem with the given list of sigs. Return whether it was successful. */
    boolean process(AlloyProblem problem);

    // What should this processor be called in output?
    String displayName();

}
