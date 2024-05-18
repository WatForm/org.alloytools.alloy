package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusOptions;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * A command processor which runs the command through Portus and dumps Fortress's SMTLIB+.
 */
final class OutputSmtlibCommandProcessor implements CommandProcessor {

    // Which solver should we use to output SMTLIB+? Determines what transformers are called.
    private final A4Options.SatSolver solver;

    public OutputSmtlibCommandProcessor(A4Options.SatSolver solver) {
        this.solver = solver;
    }

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        // Setup how we want to output the SMTLIB+ file: "filename_command.smttc" in the Alloy file's directory.
        Path alloyFilePath = Paths.get(options.originalFilename).toAbsolutePath();
        options.portusOptions.outputDirectory = alloyFilePath.getParent().toString();
        options.portusOptions.outputName = getOutputName(alloyFilePath.getFileName().toString(), command.label);
        options.solver = solver;

        options.solver.commandRunner().executeCommand(A4Reporter.NOP, world, command, options);
        System.out.println("  Done. Output to " + options.portusOptions.outputDirectory
                + FileSystems.getDefault().getSeparator()
                + options.portusOptions.outputName
                + PortusOptions.SMTLIBPLUS_EXTENSION);
        return true;
    }

    private String getOutputName(String filename, String commandLabel) {
        // strip ".als" from the filename, and add the command name separated by "_"
        if (filename.endsWith(".als")) {
            filename = filename.substring(0, filename.length() - ".als".length());
        }
        return filename + "_" + commandLabel;
    }

    @Override
    public String displayName() {
        return "Output SMTLIB+: " + solver.id();
    }

}
