package ca.uwaterloo.watform.portus.cli;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The command-line options to the CLI. Handles parsing the command-line arguments and printing help.
 */
final class PortusCLIOptions {

    // The Portus options available.
    public final Option help = new Option("-h", "Print this help.");
    public final Option verbose = new Option("-v", "Enable verbose output.");
    public final Option adjustBitwidth = new Option(
            "-b", "Adjust bitwidths to be large enough for the cardinality scope axiom strategy.");
    public final Option noTimeout = new Option("-nt", "Disable the 20-minute SMT solver timeout.");

    public final Option pickCommandNumber = new Option(
            "-command", 1, "Run the arg'th command (1-indexed) in each file if no specific command is specified.");

    public final Option fortressCompiler = new Option("-compiler", 1, Collections.singletonList("Standard"),
            "The Fortress compiler to use; see Fortress docs for options. (default: Standard)");

    public final Option fortressSolver = new Option("-solver", 1, Collections.singletonList("Z3NonIncCli"),
            "The Fortress solver to use; see Fortress docs for options. (default: Z3NonIncCli)");

    public final Option setAllScopes = new Option(
            "-all-scopes", 1, "Set the scope of all non-one, non-lone top-level sigs to this scope, exact.");
    public final Option setSigScope = new Option(
            "-scope", 2, "Set the scope of the arg1'th (1-indexed) non-one, non-lone top-level sig to arg2, exact. "
                    + "Overrides -all-scopes.");

    public final Option useRunPortusProcessor = new Option("-r", "Run Portus on each command.");
    public final Option useRunKodkodProcessor = new Option("-rk", "Run Kodkod (Sat4j) on each command.");
    public final Option useRunKodkodMiniSatProcessor = new Option("-rk-ms", "Run Kodkod (MiniSat) on each command.");

    public final Option useCorrectnessProcessor = new Option("-c", "Check Portus correctness on each command.");
    public final Option useDeltaDebugProcessor = new Option(
            "-dd", "Run delta debugging on each command to minimize the model (experimental).");
    public final Option useOutputPreSmtlibProcessor = new Option(
            "-smtlib-tc", "Output SMTLIB+ (typechecking only) for each command.");
    public final Option useOutputPostSmtlibProcessor = new Option(
            "-smtlib-all", "Output SMTLIB+ (post-Fortress) for each command.");
    public final Option useCheckSupportProcessor = new Option(
            "-support", "Check whether Portus supports each command.");

    public final Option useStatisticsProcessor = new Option(
            "-stats", "Output Portus translation statistics for each command without solving.");
    public final Option useCountCommandsProcessor = new Option(
            "-cmd-count", "Output a count of the commands in each file.");

    public final Option disableSimpleScalarOpt = new Option(
            "-disable-simple-scalar-opt", "Disable simple scalar optimization.");
    public final Option disableOneSigOpt = new Option(
            "-disable-one-sig-opt", "Disable one sig optimization.");
    public final Option disableJoinOpt = new Option(
            "-disable-join-opt", "Disable join optimization.");
    public final Option disableOrderingModuleOpt = new Option(
            "-disable-ordering-opt", "DEPRECATED: no-op. The ordering module optimization cannot be disabled.");
    public final Option disableMembershipPredicateOpt = new Option(
            "-disable-mem-pred-opt", "Disable membership predicate optimization.");
    public final Option disableClosureOfScalarOpt = new Option(
            "-disable-closure-scalar-opt", "Disable closure-of-scalar optimization.");
    public final Option disableIntsAsScalars = new Option(
            "-disable-ints-as-scalars", "Disable translating integer expressions using the cast-to-scalar system.");
    public final Option disablePartitionSortPolicy = new Option(
            "-disable-partition-sp", "Disable the partition sort policy, use the univ sort policy.");
    public final Option disableSumDefinitionsOpt = new Option(
            "-disable-sum-defn-opt", "Disable sum definitions optimization.");
    public final Option disableExprDefnOpt = new Option("-disable-expr-defn-opt",
            "Disable fun/pred call definition optimization.");
    public final Option disableRelationalScalarOpt = new Option("-disable-rel-scalar-opt",
            "Disable relational scalars optimization.");
    public final Option disableAntiMergePreprocessing = new Option("-disable-anti-merge",
            "Disable preprocessing to reduce sort merging. WARNING: some models will fail to translate!");
    public final Option disableFuncOpt = new Option("-disable-func-opt",
            "Disable function optimization. WARNING: some models will fail to translate!");
    public final Option useCardinalityScopeAxiomStrategy = new Option(
            "-use-card-sap", "Use the cardinality-based instead of constants-based scope axiom strategy.");
    public final Option disableAllOpts = new Option(
            "-disable-all-opts", "Shortcut: Disable all optimizations except the function optimization and the " +
            "partition sort policy, use the cardinality scope axiom strategy.");

    public final Option disableOrderingDefinition = new Option(
            "-disable-ordering-defn", "Disable using definitions in the ordering module.");
    public final Option disableClosureOptDefinition = new Option(
            "-disable-closure-opt-defn", "Disable using definitions in the closure-of-scalars optimization.");
    public final Option enableSumBalancing = new Option(
            "-enable-sum-balancing",
            "Enable balanced sum definitions (experimental). Requires sum definitions optimization.");

    public final Option enableElementOfScalarOpt = new Option(
            "-enable-element-scalar-opt", "Enable element-of scalar caster optimization (experimental).");
    public final Option enableCaching = new Option(
            "-enable-caching", "Enable caching translations (experimental).");

    public final Option enableKodkodIntCompatibility = new Option(
            "-kodkod-int-compat", "Force compatibility with Kodkod integer semantics (slow).");

    public final Option enableFortressNonExactScopes = new Option(
            "-enable-fortress-nonexact-scopes", "Enable use of the Fortress-level non-exact scopes feature.");

    public final Option noOverflow = new Option("-no-overflow", "Turn on 'prevent overflow' when running with Kodkod.");

    public final Option[] allOptions = new Option[] {
            help, verbose, adjustBitwidth, noTimeout, pickCommandNumber,
            fortressCompiler, fortressSolver,
            setAllScopes, setSigScope,
            useRunPortusProcessor, useRunKodkodProcessor, useRunKodkodMiniSatProcessor,
            useCorrectnessProcessor, useDeltaDebugProcessor,
            useOutputPreSmtlibProcessor, useOutputPostSmtlibProcessor, useCheckSupportProcessor,
            useStatisticsProcessor, useCountCommandsProcessor,
            disableSimpleScalarOpt, disableOneSigOpt, disableJoinOpt, disableOrderingModuleOpt,
            disableClosureOfScalarOpt, disableIntsAsScalars, disableMembershipPredicateOpt, disablePartitionSortPolicy,
            disableSumDefinitionsOpt, disableExprDefnOpt, disableRelationalScalarOpt,
            useCardinalityScopeAxiomStrategy, disableAntiMergePreprocessing, disableFuncOpt, disableAllOpts,
            disableOrderingDefinition, disableClosureOptDefinition, enableSumBalancing,
            enableElementOfScalarOpt, enableCaching, enableKodkodIntCompatibility,
            enableFortressNonExactScopes,
            noOverflow,
    };

    // The positional arguments - a list of Alloy command specifiers.
    public final List<String> specifiers = new ArrayList<>();

    private final Map<Option, List<String>> activeOptionsToArgs = new HashMap<>();

    public PortusCLIOptions(String[] args, String programName) {
        // parse through the args manually
        int idx = 0;
        while (idx < args.length) {
            boolean foundOption = false;
            for (Option option : allOptions) {
                if (option.name.equals(args[idx])) {
                    // don't allow options to be specified multiple times
                    if (option.active()) {
                        System.err.println("Error: option " + option.name
                                + " cannot be specified multiple times.");
                        printHelp(programName);
                        throw new IllegalArgumentException();
                    }

                    // it's an option - capture its arguments
                    List<String> optionArgs = new ArrayList<>();
                    idx++; // advance past the option itself

                    for (int i = 0; i < option.arity; i++) {
                        if (idx >= args.length) {
                            System.err.println("Error: not enough arguments for option: " + option.name
                                    + " (expected " + option.arity + ")");
                            printHelp(programName);
                            throw new IllegalArgumentException();
                        }
                        optionArgs.add(args[idx]);
                        idx++;
                    }

                    // set the option active and move on
                    activeOptionsToArgs.put(option, optionArgs);
                    foundOption = true;
                    break;
                }
            }

            if (!foundOption) {
                // not an option - it's a specifier
                specifiers.add(args[idx]);
                idx++;
            }
        }
    }

    public void printHelp(String programName) {
        System.err.println("Usage: " + programName + " [options] <Alloy filenames/specifiers>");
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

    public class Option {

        private final String name;
        private final int arity;
        private final List<String> defaultArgs;

        private final String help;

        public Option(String name, int arity, List<String> defaultArgs, String help) {
            if (name == null || help == null) {
                throw new NullPointerException();
            }
            if (defaultArgs != null && defaultArgs.size() != arity) {
                throw new IllegalArgumentException("Default arguments must have same size as arity!");
            }
            this.name = name;
            this.help = help;
            this.defaultArgs = defaultArgs;
            this.arity = arity;
        }

        // Default to no default args
        public Option(String name, int arity, String help) {
            this(name, arity, null, help);
        }

        // Default to 0-ary
        public Option(String name, String help) {
            this(name, 0, null, help);
        }

        public String name() {
            return name;
        }

        // Is the option enabled?
        public boolean active() {
            return activeOptionsToArgs.containsKey(this);
        }

        // Get the arguments passed to the option; if there are no default arguments, must be active.
        public List<String> arguments() {
            if (!active()) {
                if (defaultArgs != null) {
                    return defaultArgs;
                } else {
                    throw new IllegalArgumentException("Option is not active!");
                }
            }
            return activeOptionsToArgs.get(this);
        }

        public String singleArgument() {
            if (arity != 1) throw new IllegalArgumentException("Can only call singleArgument() on a unary Option!");
            return arguments().get(0);
        }

        // What should we display the option as for printing?
        public String displayName() {
            StringBuilder builder = new StringBuilder(name);
            for (int i = 0; i < arity; i++) {
                builder.append(" <arg");
                if (arity > 1) {
                    builder.append(i + 1);
                }
                builder.append(">");
            }
            return builder.toString();
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Option option = (Option) o;
            return arity == option.arity && name.equals(option.name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name, arity);
        }

    }

    public class EnumOption extends Option {

        private final List<String> alternatives;
        private final String defaultAlternative;

        public EnumOption(String name, List<String> alternatives, String defaultAlterative, String help) {
            super(name, 1, help + " " + makeExtraEnumHelp(alternatives, defaultAlterative));
            if (!alternatives.contains(defaultAlterative)) {
                throw new IllegalArgumentException("Default must be an alternative!");
            }
            this.alternatives = alternatives;
            this.defaultAlternative = defaultAlterative;
        }

        public String chosen() {
            return active() ? arguments().get(0) : defaultAlternative;
        }

        public boolean validate() {
            return alternatives.contains(chosen());
        }

    }

    private static String makeExtraEnumHelp(List<String> alternatives, String defaultAlternative) {
        StringBuilder extra = new StringBuilder("Options: ");
        for (int idx = 0; idx < alternatives.size(); idx++) {
            if (idx > 0) {
                extra.append(", ");
            }
            String alternative = alternatives.get(idx);
            extra.append(alternative);
            if (alternative.equals(defaultAlternative)) {
                extra.append(" (default)");
            }
        }
        extra.append(".");
        return extra.toString();
    }

}
