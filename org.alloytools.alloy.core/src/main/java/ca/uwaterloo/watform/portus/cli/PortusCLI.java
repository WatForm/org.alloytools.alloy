package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.*;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * A CLI for testing Portus.
 * Given a list of Alloy files on the command line, runs them through various command processors.
 */
public final class PortusCLI {

    private static final String PROGRAM_NAME = "portus";

    /**
     * Return a new command with bitwidth adjusted high enough to be able to represent the scope of every sort,
     * so the cardinality scope axiom strategy will work. Also return the old bitwidth.
     * TODO: this is an ugly hack, can we move it into the main portus package?
     */
    private static Pair<Integer, Command> fixBitwidthForCardinalityScope(
            Module world, Command command, A4Options options) {
        Iterable<Sig> sigs = world.getAllReachableSigs();
        ScopeComputer scoper = ScopeComputer.compute(A4Reporter.NOP, options, sigs, command).b;
        ModelInfo modelInfo = new ModelInfo(sigs, command, scoper);
        NameGenerator nameGenerator = new SanitizingNameGenerator();

        if (options.portusOptions.enableAntiMergePreprocessing) {
            // Preprocess the formula - TODO duplicating TranslateAlloyToFortress, ugly!
            AntiMergePreprocessor preprocessor = new AntiMergePreprocessor(
                    sigs, command, modelInfo, scoper, nameGenerator);
            command = preprocessor.preprocess(command);
        }

        SortPolicy sortPolicy = options.portusOptions.getSortPolicy(
                new PortusStatistics(), sigs, command, modelInfo, scoper, nameGenerator);

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

    private static int parseInt(String str, String error, PortusCLIOptions options) {
        try {
            return Integer.parseInt(str);
        } catch (NumberFormatException e) {
            System.err.println(error);
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
            return -1;
        }
    }

    private static void applyOptionFlags(PortusOptions options, PortusCLIOptions cliOptions) {
        if (cliOptions.disableOrderingModuleOpt.active()) {
            System.err.println("Warning: " + cliOptions.disableOrderingModuleOpt.name()
                    + " is a no-op because the ordering module optimization cannot be"
                    + " disabled for correctness reasons.");
        }

        options.verbose = cliOptions.verbose.active();

        boolean disableAllOpts = cliOptions.disableAllOpts.active();
        options.enableSimpleScalarOptimization = !disableAllOpts && !cliOptions.disableSimpleScalarOpt.active();
        options.enableOneSigOptimization = !disableAllOpts && !cliOptions.disableOneSigOpt.active();
        options.enableJoinOptimization = !disableAllOpts && !cliOptions.disableJoinOpt.active();
        options.enableMembershipPredicateOptimization = !disableAllOpts
                && !cliOptions.disableMembershipPredicateOpt.active();
        options.enableClosureOfScalarOptimization = !disableAllOpts && !cliOptions.disableClosureOfScalarOpt.active();
        options.enableIntsAsScalars = !disableAllOpts && !cliOptions.disableIntsAsScalars.active();
        options.enablePartitionSortPolicy = !disableAllOpts && !cliOptions.disablePartitionSortPolicy.active();
        options.enableSumDefinitionsOptimization = !disableAllOpts && !cliOptions.disableSumDefinitionsOpt.active();
        options.enableExprDefnOptimization = !disableAllOpts && !cliOptions.disableExprDefnOpt.active();
        options.enableRelationalScalarOptimization = !disableAllOpts && !cliOptions.disableRelationalScalarOpt.active();
        // specifically don't include the function optimization in disableAllOpts
        options.enableFuncOptimization = !cliOptions.disableFuncOpt.active();
        options.enableConstantsScopeAxiomStrategy = !disableAllOpts
                && !cliOptions.useCardinalityScopeAxiomStrategy.active();
        options.enableAntiMergePreprocessing = !disableAllOpts && !cliOptions.disableAntiMergePreprocessing.active();

        options.enableOrderingDefinition = !cliOptions.disableOrderingDefinition.active();
        options.enableClosureOptDefinition = !cliOptions.disableClosureOptDefinition.active();
        options.enableSumBalancing = cliOptions.enableSumBalancing.active();

        options.enableElementOfScalarOptimization = cliOptions.enableElementOfScalarOpt.active();
        options.enableCaching = cliOptions.enableCaching.active();

        options.enableKodkodIntCompatibility = cliOptions.enableKodkodIntCompatibility.active();

        options.enableFortressNonExactScopes = cliOptions.enableFortressNonExactScopes.active();
    }

    private static void setFortressOptions(PortusOptions options, PortusCLIOptions cliOptions) {
        options.fortressCompiler = cliOptions.fortressCompiler.singleArgument();
        options.fortressSolver = cliOptions.fortressSolver.singleArgument();
    }

    private static boolean canOverrideSig(Sig sig) {
        return sig.isTopLevel() && sig.isOne == null && sig.isLone == null && sig.isEnum == null;
    }

    private static void validateScope(int scope, PortusCLIOptions options) {
        if (scope < 0) {
            System.err.println("Error: scope cannot be negative");
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        }
    }

    // Use this instead of command.change(sig, exact, scope) because it mishandles the case where the scope for the sig
    // is (presumably erroneously) specified twice:
    //   sig A {}
    //   run {} for 3 A, 3 A
    // This is valid iff the duplicate scopes are the same. command.change(sig, exact, scope) only changes the first
    // scope, leading to an error. This changes all of the scopes.
    private static Command changeScope(Command command, Sig sig, boolean exact, int scope) {
        AtomicBoolean foundAny = new AtomicBoolean(false);
        List<CommandScope> newScopes = command.scope.stream().map(cmdScope -> {
            if (cmdScope.sig == sig) {
                foundAny.set(true);
                return new CommandScope(cmdScope.pos, cmdScope.sigPos, sig, exact, scope, scope, 1);
            } else {
                return cmdScope;
            }
        }).collect(Collectors.toList());

        if (foundAny.get()) {
            return command.change(ConstList.make(newScopes));
        } else {
            CommandScope cmdScope = new CommandScope(Pos.UNKNOWN, Pos.UNKNOWN, sig, exact, scope, scope, 1);
            return command.change(Util.append(command.scope, cmdScope));
        }
    }

    private static Command setDefaultOverall(Command command) {
        final int defaultOverall = 3;
        return new Command(
                command.pos, command.nameExpr, command.label, command.check, defaultOverall, command.bitwidth,
                command.maxseq, command.minprefix, command.maxprefix, command.expects, command.scope,
                command.additionalExactScopes, command.commandKeyword, command.formula, command.parent);
    }

    // Implement the setAllScopes and setSigScope options
    private static Command performScopeOverrides(Module world, Command command, PortusCLIOptions options) {
        List<Sig> overridableSigs = world.getAllReachableUserDefinedSigs().stream()
                .filter(PortusCLI::canOverrideSig)
                .collect(Collectors.toList());

        if (options.setAllScopes.active()) {
            int scope = parseInt(options.setAllScopes.arguments().get(0),
                    "Error: " + options.setAllScopes.name() + " argument must be an integer", options);
            validateScope(scope, options);
            System.out.println("Setting all scopes to " + scope);
            for (Sig sig : overridableSigs) {
                command = changeScope(command, sig, true, scope);
            }
        }

        if (options.setSigScope.active()) {
            // ScopeComputer will throw an error if command.overall < 0 (i.e. no overall scope specified) and not every
            // top-level sig has a separate scope specified. Therefore, if we're adding a scope to a command with no
            // overall scope specified and multiple top-level sigs, manually set the overall scope to the default (3) to
            // preserve the previously-implied scopes.
            if (command.overall < 0 && command.scope.isEmpty() && overridableSigs.size() > 1) {
                System.out.println("NOTE: setting default overall for this command!");
                command = setDefaultOverall(command);
            }

            String error = "Error: " + options.setSigScope.name() + "arguments must be integers";
            int whichSig = parseInt(options.setSigScope.arguments().get(0), error, options);
            int scope = parseInt(options.setSigScope.arguments().get(1), error, options);

            if (whichSig < 1 || whichSig > overridableSigs.size()) {
                System.err.println("Error: invalid sig number '" + whichSig + "' (1-indexed) for "
                        + options.setSigScope.name() + ": there are only " + overridableSigs.size()
                        + " non-one, non-lone top-level sigs");
                options.printHelp(PROGRAM_NAME);
                System.exit(-1);
            }
            validateScope(scope, options);

            Sig sig = overridableSigs.get(whichSig - 1); // convert to 0-indexed
            System.out.println("Setting scope of " + sig.label + " to " + scope);
            command = changeScope(command, sig, true, scope);
        }

        return command;
    }

    /** Process a single command in an Alloy file with each of the chosen processors. Return whether all successful. */
    private static boolean processCommand(Module world, Command command, A4Options alloyOptions,
                                          PortusCLIOptions options, List<CommandProcessor> processors) {
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

        command = performScopeOverrides(world, command, options);

        boolean allSuccessful = true;
        for (CommandProcessor processor : processors) {
            System.out.println("Running with processor: " + processor.displayName());
            boolean success;
            try {
                success = processor.process(world, command, alloyOptions);
            } catch (TimeoutException e) {
                System.out.println("  SMT solver timeout!");
                success = false;
            } catch (Exception e) {
                System.out.println("  EXCEPTION:");
                e.printStackTrace();
                success = false;
            }
            allSuccessful = allSuccessful && success;
        }
        return allSuccessful;
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

    /** Process all the commands in an Alloy file. Return true iff all of them succeeded. */
    private static boolean processSpecifier(String specifier, PortusCLIOptions options,
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
            alloyOptions.noOverflow = options.noOverflow.active();
            applyOptionFlags(alloyOptions.portusOptions, options);
            setFortressOptions(alloyOptions.portusOptions, options);

            if (options.noTimeout.active()) {
                // Set the timeout to something silly like 20 days
                alloyOptions.portusOptions.timeoutMillis = 20 * 24 * 60 * 60 * 1000;
            }

            // If no command names were specified and the option to run the nth command is specified,
            // run only that command.
            if (runAllCommands && options.pickCommandNumber.active()) {
                int commandIndex = parsePickCommandNumber(options, commands.size(), alloyFilename);
                Command command = commands.get(commandIndex);
                return processCommand(world, command, alloyOptions, options, processors);
            }

            boolean allSuccessful = true;
            for (Command command : commands) {
                if (runAllCommands || commandNames.contains(command.label)) {
                    boolean success = processCommand(world, command, alloyOptions, options, processors);
                    allSuccessful = allSuccessful && success;
                }
            }
            return allSuccessful;
        } catch (Exception e) {
            System.err.println("EXCEPTION:");
            e.printStackTrace();
            return false;
        }
    }

    private static int parsePickCommandNumber(PortusCLIOptions options, int numCommands, String filename) {
        if (!options.pickCommandNumber.active()) {
            return -1;
        }

        String argument = options.pickCommandNumber.arguments().get(0);
        int passedNumber = parseInt(argument, "Error: invalid command number: " + argument, options);

        // User passes 1-indexed command number, convert to 0-indexed
        int commandNumber = passedNumber - 1;
        if (commandNumber < 0) {
            System.err.println("Error: invalid command number (must be postive and 0-indexed): " + argument);
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        } else if (commandNumber >= numCommands) {
            System.err.println("Error: command number " + argument + " is too large, there are only "
                    + numCommands + " command(s) in " + filename);
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        }
        return commandNumber;
    }

    /** Get a list of all the processors to use based on the options. */
    private static List<CommandProcessor> getCommandProcessors(PortusCLIOptions options) {
        // This could be abstracted if needed, but it's probably fine.
        List<CommandProcessor> processors = new ArrayList<>();
        if (options.useStatisticsProcessor.active()) {
            processors.add(new StatisticsCommandProcessor());
        }
        if (options.useCountCommandsProcessor.active()) {
            processors.add(new CountCommandsCommandProcessor());
        }
        if (options.useRunPortusProcessor.active()) {
            processors.add(new RunCommandProcessor(A4Options.SatSolver.Z3));
        }
        if (options.useRunKodkodProcessor.active()) {
            processors.add(new RunCommandProcessor(A4Options.SatSolver.SAT4J));
        }
        if (options.useRunKodkodMiniSatProcessor.active()) {
            processors.add(new RunCommandProcessor(A4Options.SatSolver.MiniSatJNI));
        }
        if (options.useCorrectnessProcessor.active()) {
            processors.add(new CorrectnessCommandProcessor(new CorrectnessChecker()));
        }
        if (options.useDeltaDebugProcessor.active()) {
            processors.add(new DeltaDebugCommandProcessor());
        }
        if (options.useOutputPreSmtlibProcessor.active()) {
            processors.add(new OutputSmtlibCommandProcessor(A4Options.SatSolver.PRE_FORTRESS_SMTLIB));
        } else if (options.useOutputPostSmtlibProcessor.active()) { // don't do both - confusing
            processors.add(new OutputSmtlibCommandProcessor(A4Options.SatSolver.POST_FORTRESS_SMTLIB));
        }
        if (options.useCheckSupportProcessor.active()) {
            processors.add(new CheckSupportCommandProcessor());
        }
        return processors;
    }

    public static void main(String[] args) {
        PortusCLIOptions options;
        try {
            options = new PortusCLIOptions(args, PROGRAM_NAME);
        } catch (IllegalArgumentException e) {
            System.exit(-1);
            return;
        }

        if (options.help.active()) {
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        }

        if (options.specifiers.isEmpty()) {
            System.err.println("Error: no Alloy filenames/specifiers specified");
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        }

        List<CommandProcessor> processors = getCommandProcessors(options);
        if (processors.isEmpty()) {
            System.err.println("Error: no command processing options specified.");
            options.printHelp(PROGRAM_NAME);
            System.exit(-1);
        }

        boolean allSuccessful = true;
        for (String specifier : options.specifiers) {
            boolean success = processSpecifier(specifier, options, processors);
            allSuccessful = allSuccessful && success;
        }

        System.exit(allSuccessful ? 0 : 1);
    }

}
