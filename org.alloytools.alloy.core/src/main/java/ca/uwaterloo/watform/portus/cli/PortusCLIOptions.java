package ca.uwaterloo.watform.portus.cli;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * The command-line options to the CLI. Handles parsing the command-line arguments and printing help.
 */
final class PortusCLIOptions {

    // The Portus options available.
    public final Option help = new Option("-h", "Print this help");
    public final Option adjustBitwidth = new Option(
            "-b", "Adjust bitwidths to be large enough for the cardinality scope axiom strategy");

    public final Option useCorrectnessProcessor = new Option("-c", "Check Portus correctness on each command.");
    public final Option useOutputPreSmtlibProcessor = new Option(
            "-smtlib-tc", "Output SMTLIB+ (typechecking only) for each command.");
    public final Option useOutputPostSmtlibProcessor = new Option(
            "-smtlib-all", "Output SMTLIB+ (post-Fortress) for each command.");

    public final Option[] allOptions = new Option[] {
            help, adjustBitwidth, useCorrectnessProcessor, useOutputPreSmtlibProcessor, useOutputPostSmtlibProcessor,
    };

    // The positional arguments - a list of Alloy filenames.
    public final List<String> alloyFilenames;

    private final List<String> args;

    public PortusCLIOptions(String[] args) {
        this.args = Arrays.asList(args);
        // filter out all the options
        this.alloyFilenames = this.args.stream()
                .filter(arg -> Arrays.stream(allOptions).noneMatch(option -> option.name.equals(arg)))
                .collect(Collectors.toList());
    }

    public void printHelp(String programName) {
        System.err.println("Usage: " + programName + " [flags] <Alloy files...>");
        System.err.println("Options:");
        for (Option option : allOptions) {
            System.err.println("\t" + option.displayName() + "\t" + option.help);
        }
    }

    // We only support flag options (0-ary) for now.
    public final class Option {

        private final String name;
        private final String help;

        public Option(String name, String help) {
            this.name = name;
            this.help = help;
        }

        // Is the option enabled?
        public boolean active() {
            return args.contains(name);
        }

        // What should we display the option as for printing?
        public String displayName() {
            return name;
        }

    }

}
