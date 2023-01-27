package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * Something that can process an Alloy command in a way we might want to invoke from the CLI.
 * Implementations will be run once for every command in an Alloy file.
 */
interface CommandProcessor {

    void process(Iterable<Sig> sigs, Command command, A4Options options);

    // What should this processor be called in output?
    String displayName();

}
