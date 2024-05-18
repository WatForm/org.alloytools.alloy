package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;

/**
 * A quick-n-dirty CLI which counts the number of commands in an Alloy file for use in scripts.
 */
public class CommandCounterCLI {

    public static void main(String[] args) {
        if (args.length != 1) {
            System.err.println("CommandCounterCLI expects one argument: an Alloy filename.");
            System.exit(-1);
        }

        String filename = args[0];
        Module world = CompUtil.parseEverything_fromFile(null, null, filename);
        System.out.println(world.getAllCommands().size());
    }

}
