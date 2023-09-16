package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.SortPolicy;
import ca.uwaterloo.watform.portus.TimeoutException;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A CLI for testing Portus.
 * Given a list of Alloy files on the command line, runs them through various command processors.
 */
public final class PortusCLI {

    private static final String PROGRAM_NAME = "PortusCLI";

    /**
     * Return a new command with bitwidth adjusted high enough to be able to represent the scope of every sort,
     * so the cardinality scope axiom strategy will work. Also return the old bitwidth.
     * TODO: this is an ugly hack, can we move it into the main portus package?
     */
    private static Pair<Integer, Command> fixBitwidthForCardinalityScope(
            Module world, Command command, A4Options options) {
        Iterable<Sig> sigs = world.getAllReachableSigs();
        ScopeComputer scoper = ScopeComputer.compute(A4Reporter.NOP, options, sigs, command).b;
        SortPolicy sortPolicy = options.portusOptions.getSortPolicy(sigs, command, scoper);

        // find the smallest bitwidth >= the command's bitwidth such that the max int representable is >= the size
        // of all sorts created by the sort policy
        int bitwidth = scoper.getBitwidth();
        for (Sig sig : world.getAllReachableUserDefinedSigs()) {
            int sortScope = sortPolicy.getSortScope(sortPolicy.getSort(sig));
            // bump up the bitwidth until it can represent sortScope
            while (Util.max(bitwidth) < sortScope) {
                bitwidth++;
            }
        }

        // replace the command's bitwidth but keep everything else the same
        Command newCommand = new Command(
                command.pos, command.nameExpr, command.label, command.check, command.overall, bitwidth, command.maxseq,
                command.minprefix, command.maxprefix, command.expects, command.scope, command.additionalExactScopes,
                command.commandKeyword, command.formula, command.parent);
        return new Pair<>(scoper.getBitwidth(), newCommand);
    }

    private static void applyOptimizationFlags(PortusOptions options, PortusCLIOptions cliOptions) {
        boolean disableAll = cliOptions.disableAllOpts.active();
        options.enableSimpleScalarOptimization = !disableAll && !cliOptions.disableSimpleScalarOpt.active();
        options.enableOneSigOptimization = !disableAll && !cliOptions.disableOneSigOpt.active();
        options.enableJoinOptimization = !disableAll && !cliOptions.disableJoinOpt.active();
        options.enableOrderingModuleOptimization = !disableAll && !cliOptions.disableOrderingModuleOpt.active();
        options.enableMembershipPredicateOptimization = !disableAll
                && !cliOptions.disableMembershipPredicateOpt.active();
        options.enablePartitionSortPolicy = !disableAll && !cliOptions.disablePartitionSortPolicy.active();
        options.enableConstantsScopeAxiomStrategy = !disableAll
                && !cliOptions.useCardinalityScopeAxiomStrategy.active();
    }

    /** Process a single command in an Alloy file with each of the chosen processors. */
    private static void processCommand(Module world, Command command, A4Options alloyOptions, PortusCLIOptions options,
                                       List<CommandProcessor> processors) {
        System.out.println("Command: " + command.label);

        if (options.adjustBitwidth.active()) {
            // Fix the command bitwidth to avoid errors when using the cardinality scope axiom strategy
            Pair<Integer, Command> fixed = fixBitwidthForCardinalityScope(world, command, alloyOptions);
            int oldBitwidth = fixed.a;
            Command newCommand = fixed.b;
            if (oldBitwidth != newCommand.bitwidth) {
                System.out.println("WARNING: bumped bitwidth from " + oldBitwidth + " to " + newCommand.bitwidth
                        + " to meet requirements of cardinality scope axiom strategy (enabled due to "
                        + options.adjustBitwidth.displayName() + ")");
                command = newCommand;
            }
        }

        for (CommandProcessor processor : processors) {
            System.out.println("Running with processor: " + processor.displayName());
            try {
                processor.process(world.getAllReachableSigs(), command, alloyOptions);
            } catch (TimeoutException e) {
                System.out.println("  SMT solver timeout!");
            } catch (Exception e) {
                System.out.println("  EXCEPTION:");
                e.printStackTrace();
            }
        }
    }

    // specifier format: filename [: command_name [, command_name]*]
    private static final Pattern SPECIFIER_PATTERN = Pattern.compile(
            "(?<filename>[^:]*)(:(?<commands>.*))?");

    private static Pair<String, String[]> splitSpecifier(String specifier) {
        Matcher matcher = SPECIFIER_PATTERN.matcher(specifier);
        if (!matcher.matches()) {
            // shouldn't be possible
            throw new IllegalArgumentException("Invalid specifier " + specifier + " (this shouldn't be possible)");
        }

        String filename = matcher.group("filename");
        String commandNamesRaw = matcher.group("commands");
        String[] commandNames = commandNamesRaw == null ? new String[0] : commandNamesRaw.split(",");
        return new Pair<>(filename, commandNames);
    }

    /** Process all the commands in an Alloy file. */
    private static void processSpecifier(String specifier, PortusCLIOptions options,
                                         List<CommandProcessor> processors) {
        System.out.println("Processing " + specifier + "...");

        Pair<String, String[]> split = splitSpecifier(specifier);
        String alloyFilename = split.a;
        Set<String> commandNames = new HashSet<>(Arrays.asList(split.b));
        boolean runAllCommands = commandNames.isEmpty();

        try {
            Module world = CompUtil.parseEverything_fromFile(null, null, alloyFilename);
            List<Command> commands = world.getAllCommands();

            A4Options alloyOptions = new A4Options();
            alloyOptions.originalFilename = alloyFilename;
            applyOptimizationFlags(alloyOptions.portusOptions, options);

            if (options.noTimeout.active()) {
                // Set the timeout to something silly like 20 days
                alloyOptions.portusOptions.timeoutMillis = 20 * 24 * 60 * 60 * 1000;
            }

            for (Command command : commands) {
                if (runAllCommands || commandNames.contains(command.label)) {
                    processCommand(world, command, alloyOptions, options, processors);
                }
            }
        } catch (Exception e) {
            System.err.println("EXCEPTION:");
            e.printStackTrace();
        }
    }

    /** Get a list of all the processors to use based on the options. */
    private static List<CommandProcessor> getCommandProcessors(PortusCLIOptions options) {
        // This could be abstracted if needed, but it's probably fine.
        List<CommandProcessor> processors = new ArrayList<>();
        if (options.useRunPortusProcessor.active()) {
            processors.add(new RunCommandProcessor(A4Options.SatSolver.Z3));
        }
        if (options.useRunKodkodProcessor.active()) {
            processors.add(new RunCommandProcessor(A4Options.SatSolver.SAT4J));
        }
        if (options.useCorrectnessProcessor.active()) {
            processors.add(new CorrectnessCommandProcessor());
        }
        if (options.useOutputPreSmtlibProcessor.active()) {
            processors.add(new OutputSmtlibCommandProcessor(A4Options.SatSolver.PRE_FORTRESS_SMTLIB));
        } else if (options.useOutputPostSmtlibProcessor.active()) { // don't do both - confusing
            processors.add(new OutputSmtlibCommandProcessor(A4Options.SatSolver.POST_FORTRESS_SMTLIB));
        }
        return processors;
    }

    public static void main(String[] args) {
        PortusCLIOptions options = new PortusCLIOptions(args);
        if (options.help.active()) {
            options.printHelp(PROGRAM_NAME);
            return;
        }

        if (options.specifiers.isEmpty()) {
            System.err.println("Error: no Alloy filenames/specifiers specified");
            options.printHelp(PROGRAM_NAME);
            return;
        }

        List<CommandProcessor> processors = getCommandProcessors(options);
        if (processors.size() == 0) {
            System.err.println("Error: no command processing options specified.");
            options.printHelp(PROGRAM_NAME);
            return;
        }

        for (String specifier : options.specifiers) {
            processSpecifier(specifier, options, processors);
        }
    }

}
