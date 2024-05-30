package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

final class CountCommandsCommandProcessor implements CommandProcessor {

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        System.out.println("Command count: " + world.getAllCommands().size());
        return true;
    }

    @Override
    public String displayName() {
        return "Count Commands";
    }

}
