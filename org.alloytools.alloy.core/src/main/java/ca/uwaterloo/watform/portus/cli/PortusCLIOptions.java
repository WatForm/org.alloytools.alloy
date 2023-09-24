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
    public final Option noTimeout = new Option("-nt", "Disable the 20-minute SMT solver timeout");

    public final Option useRunPortusProcessor = new Option("-r", "Run Portus on each command.");
    public final Option useRunKodkodProcessor = new Option("-rk", "Run Kodkod (Sat4j) on each command.");
    public final Option useCorrectnessProcessor = new Option("-c", "Check Portus correctness on each command.");
    public final Option useDeltaDebugProcessor = new Option(
            "-dd", "Run delta debugging on each command to minimize the model.");
    public final Option useOutputPreSmtlibProcessor = new Option(
            "-smtlib-tc", "Output SMTLIB+ (typechecking only) for each command.");
    public final Option useOutputPostSmtlibProcessor = new Option(
            "-smtlib-all", "Output SMTLIB+ (post-Fortress) for each command.");

    public final Option disableSimpleScalarOpt = new Option(
            "-disable-simple-scalar-opt", "Disable simple scalar optimization.");
    public final Option disableOneSigOpt = new Option(
            "-disable-one-sig-opt", "Disable one sig optimization.");
    public final Option disableJoinOpt = new Option(
            "-disable-join-opt", "Disable join optimization.");
    public final Option disableOrderingModuleOpt = new Option(
            "-disable-ordering-opt", "Disable ordering module optimization.");
    public final Option disableMembershipPredicateOpt = new Option(
            "-disable-mem-pred-opt", "Disable membership predicate optimization.");
    public final Option disablePartitionSortPolicy = new Option(
            "-disable-partition-sp", "Disable the partition sort policy, use the univ sort policy.");
    public final Option useCardinalityScopeAxiomStrategy = new Option(
            "-use-card-sap", "Use the cardinality-based instead of constants-based scope axiom strategy.");
    public final Option disableAllOpts = new Option(
            "-disable-all-opts", "Shortcut: Disable all optimizations and the partition sort policy, " +
            "use the cardinality scope axiom strategy");
    public final Option enableElementOfScalarOpt = new Option(
            "-enable-element-scalar-opt", "Enable element-of scalar caster optimization (experimental.");

    public final Option[] allOptions = new Option[] {
            help, adjustBitwidth, noTimeout,
            useRunPortusProcessor, useRunKodkodProcessor,
            useCorrectnessProcessor, useDeltaDebugProcessor,
            useOutputPreSmtlibProcessor, useOutputPostSmtlibProcessor,
            disableSimpleScalarOpt, disableOneSigOpt, disableJoinOpt, disableOrderingModuleOpt,
            disableMembershipPredicateOpt, disablePartitionSortPolicy, useCardinalityScopeAxiomStrategy,
            disableAllOpts, enableElementOfScalarOpt,
    };

    // The positional arguments - a list of Alloy command specifiers.
    public final List<String> specifiers;

    private final List<String> args;

    public PortusCLIOptions(String[] args) {
        this.args = Arrays.asList(args);
        // filter out all the options
        this.specifiers = this.args.stream()
                .filter(arg -> Arrays.stream(allOptions).noneMatch(option -> option.name.equals(arg)))
                .collect(Collectors.toList());
    }

    public void printHelp(String programName) {
        System.err.println("Usage: " + programName + " [flags] <Alloy filenames/specifiers>");
        System.err.println("A specifier consists of an Alloy filename, optionally followed by a colon and a");
        System.err.println("comma-separated list of command names to run. For example:");
        System.err.println("  test.als:command1,command2,command3");

        if (allOptions.length == 0) {
            return;
        }

        System.err.println("Options:");

        int longestOptionLength = Arrays.stream(allOptions)
                .map(Option::displayName)
                .map(String::length)
                .max(Integer::compareTo).get();

        for (Option option : allOptions) {
            System.err.print("  " + option.displayName());

            // pad the display name so it's uniform
            for (int padIdx = option.displayName().length(); padIdx < longestOptionLength; padIdx++) {
                System.err.print(" ");
            }

            System.err.println("  " + option.help);
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
