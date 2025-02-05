package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.compilers.AlmostNothingCompiler;
import fortress.compilers.CompilerError;
import fortress.compilers.CompilerResult;
import fortress.data.NameGenerator;
import fortress.interpretation.BasicInterpretation;
import fortress.interpretation.Interpretation;
import fortress.modelfinders.ErrorResult;
import fortress.modelfinders.ModelFinder;
import fortress.modelfinders.ModelFinderResult;
import fortress.modelfinders.StandardModelFinder;
import fortress.msfol.*;
import fortress.operations.SmtlibConverter;
import fortress.solvers.Solver;
import fortress.util.Dump;
import fortress.util.Milliseconds;
import scala.collection.immutable.Seq;
import scala.util.Either;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

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
            A4Reporter reporter, List<Sig> sigs, Command command, A4Options options) {
        return executeCommand(reporter, new PortusStatistics(), sigs, command, options);
    }

    /**
     * Execute a command. Throws {@link TimeoutException} if the solver times out.
     */
    public AlloySolution executeCommand(
            A4Reporter reporter, PortusStatistics statistics, List<Sig> sigs, Command command, A4Options options) {
        PortusLogger logger = new PortusLogger(reporter);
        AlloyProblem problem = new AlloyProblem(sigs, command, options);

        statistics.onStartPortus();
        try {
            // Actually execute the command, and time it.
            logger.translationStarted(options.solver.id(), problem.getBitwidth(), problem.getMaxSeq());

            TranslationResult translated = translate(reporter, statistics, problem);

            logger.translationFinished(translated.getTheory());

            // Intercept special-case solvers if necessary.
            if (options.solver.id().equals(A4Options.SatSolver.FORTRESS_MSFOL.id())) {
                writeFortressToFile(logger, options, translated);
                return null;
            }
            if (options.solver.id().equals(A4Options.SatSolver.POST_FORTRESS_SMTLIB.id())
                    || options.solver.id().equals(A4Options.SatSolver.PRE_FORTRESS_SMTLIB.id())) {
                writeSmtlibToFile(logger, options, translated);
                return null;
            }
            if (options.solver.id().equals(A4Options.SatSolver.CHECK_PORTUS_SUPPORT.id())) {
                checkFortressSupport(logger, options, translated);
                return null;
            }

            Interpretation interpretation = solve(logger, statistics, translated, options);
            AlloySolution solution = new FortressSolution(
                    interpretation, translated.getEvaluator(), translated.getStringDecoder(), translated.getContext(),
                    sigs, options.originalFilename, command.toString());

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

    /** Translate the model from Alloy to Fortress without executing it. */
    public TranslationResult translate(PortusStatistics statistics, AlloyProblem problem) {
        return translate(A4Reporter.NOP, statistics, problem);
    }

    /** Translate the model from Alloy to Fortress without executing it. */
    public TranslationResult translate(A4Reporter reporter, PortusStatistics statistics, AlloyProblem problem) {
        statistics.onStartTranslation();
        try {
            // Decide on the sort policy with the options
            Iterable<Sig> sigs = problem.getSigs();
            ScopeComputer scoper = problem.makeScopeComputer(reporter);
            ModelInfo modelInfo = new ModelInfo(problem, scoper);
            NameGenerator nameGenerator = new SanitizingNameGenerator();

            if (problem.getPortusOptions().enableAntiMergePreprocessing) {
                // Preprocess the formula
                AntiMergePreprocessor preprocessor = new AntiMergePreprocessor(nameGenerator);
                problem = preprocessor.preprocess(problem);
            }

            SortPolicy sortPolicy = problem.getPortusOptions().getSortPolicy(
                    statistics, problem, modelInfo, scoper, nameGenerator);
            RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, sigs, sortPolicy, scoper);

            TranslatorManager translatorManager = new TranslatorManager(
                    problem.getPortusOptions(), statistics, modelInfo, sortPolicy, nameGenerator);
            TranslationContext context = new TranslationContext(
                    problem.getPortusOptions(), scoper, sortPolicy, rangeAssigner);

            // Perform the entire translation.
            translatorManager.runAllPasses(problem, scoper, context);

            statistics.setTheoryStats(context.getTheory());
            return new TranslationResult(translatorManager, translatorManager.getStringDecoder(), sortPolicy, context);
        } finally {
            statistics.onTranslationFinished();
        }
    }

    /** Solve the translated Fortress model. */
    private Interpretation solve(
            PortusLogger logger, PortusStatistics statistics, TranslationResult translated, A4Options options)
            throws IOException {
        try (ModelFinder finder = createModelFinder(options.portusOptions)) {
            translated.configureModelFinder(finder);
            finder.setTimeout(Milliseconds.apply(options.portusOptions.timeoutMillis));
            finder.addLogger(logger);

            statistics.onStartSmtSolver();
            ModelFinderResult result;
            try {
                result = finder.checkSat(false, false);
            } finally {
                statistics.onSmtSolverFinished();
            }

            if (result instanceof ErrorResult) {
                throw new ErrorFatal("Fortress error: " + ((ErrorResult) result).message());
            }
            if (result == ModelFinderResult.Timeout()) {
                throw new TimeoutException();
            }

            return (result == ModelFinderResult.Sat()) ? postprocessInterp(finder.viewModel(), translated) : null;
        }
    }

    /** Log whether Fortress supports the model without actually solving. */
    private void checkFortressSupport(PortusLogger logger, A4Options options, TranslationResult translated) {
        try (ModelFinder finder = createModelFinder(options.portusOptions)) {
            translated.configureModelFinder(finder);
            finder.setTimeout(Milliseconds.apply(options.portusOptions.timeoutMillis));
            finder.addLogger(logger);

            Either<CompilerError, CompilerResult> result = finder.compile(options.portusOptions.verbose, false);

            if (result.isLeft()) {
                throw new ErrorFatal("Error: Fortress does not support this model. Reason: " + result.left());
            } else {
                logger.outputHasFortressSupport();
            }
        }
    }

    private Interpretation postprocessInterp(Interpretation interpretation, TranslationResult translated) {
        // Add Int if it's not already there (sometimes it isn't)
        Map<Sort, List<Value>> sortInterpretations = new HashMap<>(interpretation.sortInterpretationsJava());
        if (!sortInterpretations.containsKey(Sort.Int())) {
            int bitwidth = translated.getBitwidth();
            sortInterpretations.put(Sort.Int(), IntStream.range(Util.min(bitwidth), Util.max(bitwidth) + 1)
                    .mapToObj(IntegerLiteral::apply)
                    .collect(Collectors.toList()));
        }
        // Convert back to Scala types
        Map<Sort, Seq<Value>> sortInterpretationsScala = new HashMap<>();
        for (Sort sort : sortInterpretations.keySet()) {
            sortInterpretationsScala.put(sort, PortusUtil.toScalaSeq(sortInterpretations.get(sort)));
        }

        // Add the function definitions from the theory because they aren't returned from Fortress
        //noinspection unchecked
        return new BasicInterpretation(
                PortusUtil.toScalaMap(sortInterpretationsScala),
                interpretation.constantInterpretations(),
                interpretation.functionInterpretations(),
                interpretation.functionDefinitions().concat(translated.getTheory().functionDefinitions()).toSet());
    }

    private ModelFinder createModelFinder(PortusOptions options) {
        ModelFinder modelFinder = new StandardModelFinder();
        modelFinder.setCompiler(options.fortressCompiler);
        modelFinder.setSolver(options.fortressSolver);
        return modelFinder;
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
            Solver solver = new Solver() {
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

            ModelFinder finder = new StandardModelFinder();
            finder.setSolver(solver);
            if (options.solver.id().equals(A4Options.SatSolver.POST_FORTRESS_SMTLIB.id())) {
                // Use all the standard transformers
                finder.setCompiler(options.portusOptions.fortressCompiler);
            } else { // PRE_FORTRESS_SMTLIB
                // Use almost nothing! (only typecheck + enums->DEs + DEs->constants)
                finder.setCompiler(new AlmostNothingCompiler());
            }

            translated.configureModelFinder(finder);
            finder.checkSat(false, false);
            writer.flush();
        }
        logger.outputFilename(smtlibFile.getAbsolutePath());
    }

}
