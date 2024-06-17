package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.compiler.ConfigurableCompiler;
import fortress.compiler.LogicCompiler;
import fortress.data.NameGenerator;
import fortress.interpretation.Interpretation;
import fortress.modelfind.CompilationModelFinder;
import fortress.modelfind.ErrorResult;
import fortress.modelfind.ModelFinder;
import fortress.modelfind.ModelFinderResult;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.operations.SmtlibConverter;
import fortress.solverinterface.SolverInterface;
import fortress.solverinterface.Z3CliInterface$;
import fortress.solverinterface.solver;
import fortress.transformers.DomainEliminationTransformer$;
import fortress.transformers.EnumEliminationTransformer$;
import fortress.transformers.TypecheckSanitizeTransformer$;
import fortress.util.Dump;
import fortress.util.Milliseconds;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * The public API for Portus. Translate an Alloy AST to a Fortress theory, then attempt
 * to solve it using Fortress.
 */
public final class TranslateAlloyToFortress implements CommandRunner {

    /**
     * Execute a command. Throws {@link TimeoutException} if the solver times out.
     */
    @Override
    public AlloySolution executeCommand(
            A4Reporter reporter, Module world, Command command, A4Options options) {
        return executeCommand(reporter, new PortusStatistics(), world, command, options);
    }

    /**
     * Execute a command. Throws {@link TimeoutException} if the solver times out.
     */
    public AlloySolution executeCommand(
            A4Reporter reporter, PortusStatistics statistics, Module world, Command command, A4Options options) {
        PortusLogger logger = new PortusLogger(reporter);
        ScopeComputer scoper = ScopeComputer.compute(reporter, options, world.getAllReachableSigs(), command).b;

        statistics.onStartPortus();
        try {
            // Actually execute the command, and time it.
            logger.translationStarted(options.solver.id(), scoper.getBitwidth(), scoper.getMaxSeq());

            TranslationResult translated = translate(statistics, world, command, scoper, options);

            logger.translationFinished(translated.getTheory());

            Interpretation interpretation = solve(logger, statistics, translated, options);
            AlloySolution solution = new FortressSolution(
                    interpretation, translated.getEvaluator(), translated.getContext(),
                    world.getAllReachableSigs(), options.originalFilename, command.toString());

            logger.outputResult(command, solution);
            return solution;
        } catch (IOException e) {
            throw new ErrorFatal("IOException in Fortress translation", e);
        } catch (TimeoutException | ErrorNoPortusSupport e) {
            // Rethrow timeout exceptions and ErrorNoPortusSupport as-is, don't wrap in ErrorFatal
            throw e;
        } catch (Throwable e) {
            // Alloy will catch it anyways, so rethrow as ErrorFatal for a more helpful debug message.
            throw new ErrorFatal(e.getMessage(), e);
        } finally {
            statistics.onPortusFinished();
        }
    }

    /**
     * Translate the command to an MSFOL theory without executing it.
     */
    public TranslationResult translate(PortusStatistics statistics, Module world, Command command, A4Options options) {
        ScopeComputer scoper = ScopeComputer.compute(A4Reporter.NOP, options, world.getAllReachableSigs(), command).b;
        return translate(statistics, world, command, scoper, options);
    }

    /** Translate the model from Alloy to Fortress. */
    private TranslationResult translate(
            PortusStatistics statistics, Module world, Command command, ScopeComputer scoper, A4Options options) {
        statistics.onStartTranslation();
        try {

            // Decide on the sort policy with the options
            Iterable<Sig> sigs = world.getAllReachableSigs();
            NameGenerator nameGenerator = new SanitizingNameGenerator();
            SortPolicy sortPolicy = options.portusOptions.getSortPolicy(sigs, command, scoper, nameGenerator);
            RangeAssigner rangeAssigner = new RangeAssigner(sigs, sortPolicy, scoper);

            TranslatorManager translatorManager = new TranslatorManager(
                    options.portusOptions, statistics, sortPolicy, nameGenerator);
            TranslationContext context = new TranslationContext(
                    options.portusOptions, scoper, sortPolicy, rangeAssigner);

            // Perform the entire translation.
            translatorManager.runAllPasses(world, command, scoper, context);

            statistics.setTheoryStats(context.getTheory());
            return new TranslationResult(translatorManager, sortPolicy, context);
        } finally {
            statistics.onTranslationFinished();
        }
    }

    /** Solve the translated Fortress model. */
    private Interpretation solve(
            PortusLogger logger, PortusStatistics statistics, TranslationResult translated, A4Options options)
            throws IOException {
        // Write raw MSFOL or SMTLIB+ to file if the appropriate solver is chosen
        if (options.solver.id().equals(A4Options.SatSolver.FORTRESS_MSFOL.id())) {
            writeFortressToFile(logger, options, translated);
            return null;
        }
        if (options.solver.id().equals(A4Options.SatSolver.POST_FORTRESS_SMTLIB.id())
                || options.solver.id().equals(A4Options.SatSolver.PRE_FORTRESS_SMTLIB.id())) {
            writeSmtlibToFile(logger, options, translated);
            return null;
        }

        try (ModelFinder finder = createModelFinder(Z3CliInterface$.MODULE$, options.portusOptions)) {
            translated.configureModelFinder(finder);
            finder.setTimeout(Milliseconds.apply(options.portusOptions.timeoutMillis));
            finder.addLogger(logger);

            statistics.onStartSmtSolver();
            ModelFinderResult result;
            try {
                result = finder.checkSat(false);
            } finally {
                statistics.onSmtSolverFinished();
            }

            if (result instanceof ErrorResult) {
                throw new ErrorFatal("Fortress error: " + ((ErrorResult) result).message());
            }
            if (result == ModelFinderResult.Timeout()) {
                throw new TimeoutException();
            }

            return (result == ModelFinderResult.Sat()) ? finder.viewModel() : null;
        }
    }

    private ModelFinder createModelFinder(SolverInterface solverInterface, PortusOptions options) {
        return new CompilationModelFinder(solverInterface) {
            @Override
            public LogicCompiler createCompiler() {
                return options.makeFortressCompiler();
            }
        };
    }

    private void writeFortressToFile(PortusLogger logger, A4Options options, TranslationResult translated)
            throws IOException {
        List<String> lines = new ArrayList<>();
        lines.add(translated.getTheory().toString());
        lines.add("Bitwidth: " + translated.getBitwidth());
        for (Sort sort : translated.getTheory().sortsJava()) {
            lines.add("Scope of " + sort.name() + ": " + translated.getSortScope(sort));
        }

        File fortressFile = options.portusOptions.createOutputFile(PortusOptions.MSFOL_EXTENSION);
        Files.write(Paths.get(fortressFile.getAbsolutePath()), lines, Charset.defaultCharset());
        logger.outputFilename(fortressFile.getAbsolutePath());
    }

    private void writeSmtlibToFile(PortusLogger logger, A4Options options, TranslationResult translated)
            throws IOException {
        // Output the SMT-LIB generated by Fortress to a file
        File smtlibFile = options.portusOptions.createOutputFile(PortusOptions.SMTLIBPLUS_EXTENSION);
        try (Writer writer = new FileWriter(smtlibFile)) {
            // The trick is to replace Fortress's solver connection (SolverSession) with one that just translates
            // everything to SMT-LIB and writes to the file.
            SmtlibConverter converter = new SmtlibConverter(writer);
            SolverInterface solverInterface = () -> new solver() {
                @Override
                public void setTheory(Theory theory) {
                    // In order to dump the scope info as well, we need to create a problem state from the theory
                    // and scopes and dump that.
                    try {
                        System.out.println("Stats of final theory:");
                        PortusStatistics.printTheoryStats(theory);
                        writer.write(Dump.problemStateToSmtlibTC(translated.getProblemState(theory)));
                    } catch (IOException e) {
                        throw new UncheckedIOException(e);
                    }
                }

                @Override
                public void addAxiom(Term axiom) {
                    converter.writeAssertion(axiom);
                }

                @Override
                public ModelFinderResult solve(Milliseconds timeoutMillis) {
                    return null;
                }

                @Override
                public Interpretation solution() {
                    return null;
                }

                @Override
                public void close() {}
            };

            ModelFinder finder;
            if (options.solver.id().equals(A4Options.SatSolver.POST_FORTRESS_SMTLIB.id())) {
                // Use all the standard transformers
                finder = createModelFinder(solverInterface, options.portusOptions);
            } else { // PRE_FORTRESS_SMTLIB
                // Use only the typechecking transformer
                finder = new CompilationModelFinder(solverInterface) {
                    @Override
                    public LogicCompiler createCompiler() {
                        ConfigurableCompiler compiler = new ConfigurableCompiler();
                        compiler.addTransformer(TypecheckSanitizeTransformer$.MODULE$);
                        compiler.addTransformer(EnumEliminationTransformer$.MODULE$);
                        compiler.addTransformer(DomainEliminationTransformer$.MODULE$);
                        return compiler;
                    }
                };
            }

            translated.configureModelFinder(finder);
            finder.checkSat(false);
            writer.flush();
        }
        logger.outputFilename(smtlibFile.getAbsolutePath());
    }

}
