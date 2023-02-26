package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.compiler.ConfigurableCompiler;
import fortress.compiler.DatatypeMethodWithRangeCompiler;
import fortress.compiler.LogicCompiler;
import fortress.interpretation.Interpretation;
import fortress.modelfind.CompilationModelFinder;
import fortress.modelfind.ErrorResult;
import fortress.modelfind.ModelFinder;
import fortress.modelfind.ModelFinderResult;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.operations.SmtlibConverter;
import fortress.problemstate.ProblemState;
import fortress.problemstate.Scope;
import fortress.solverinterface.SolverInterface;
import fortress.solverinterface.Z3CliInterface$;
import fortress.solverinterface.solver;
import fortress.transformers.DomainEliminationTransformer$;
import fortress.transformers.EnumEliminationTransformer$;
import fortress.transformers.TheoryTransformer;
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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
            A4Reporter reporter, Iterable<Sig> sigs, Command command, A4Options options) {
        ScopeComputer scoper = ScopeComputer.compute(reporter, options, sigs, command).b;
        PortusLogger logger = new PortusLogger(reporter);

        try {
            // Actually execute the command, and time it.
            logger.translationStarted(options.solver.id(), scoper.getBitwidth(), scoper.getMaxSeq());
            AlloySolution solution = executeCommand(logger, sigs, command, scoper, options);
            logger.outputResult(command, solution);
            return solution;
        } catch (IOException e) {
            throw new ErrorFatal("IOException in Fortress translation", e);
        } catch (TimeoutException e) {
            // Rethrow timeout exceptions as-is, don't wrap in ErrorFatal
            throw e;
        } catch (Throwable e) {
            // Alloy will catch it anyways, so rethrow as ErrorFatal for a more helpful debug message.
            throw new ErrorFatal(e.getMessage(), e);
        }
    }

    // Execute the command specified by command, mutating and returning solution.
    private AlloySolution executeCommand(
            PortusLogger logger, Iterable<Sig> sigs, Command command,
            ScopeComputer scoper, A4Options options) throws IOException {
        // Decide on the sort policy with the options
        SortPolicy sortPolicy = options.portusOptions.getSortPolicy(sigs, scoper);

        Translator translator = new TranslatorManager(options.portusOptions);
        TranslationContext context = new TranslationContext(options.portusOptions, scoper, sortPolicy);

        // Do sigs first, then fields, then the formula.
        // We have to do fields after sigs because a field can refer to sigs that come after it.
        translateSigs(sigs, translator, context);
        translateFields(sigs, translator, context);
        // TODO: append all the facts and field facts to the formula (copy/abstract makeFacts)
        context.addAxiom(translator.translate(command.formula, context));
        logger.translationFinished(context.getTheory());

        // Write raw MSFOL or SMTLIB+ to file if the appropriate solver is chosen
        if (options.solver.id().equals(A4Options.SatSolver.FORTRESS_MSFOL.id())) {
            writeFortressToFile(logger, options, context);
            return null;
        }
        if (options.solver.id().equals(A4Options.SatSolver.POST_FORTRESS_SMTLIB.id())
            || options.solver.id().equals(A4Options.SatSolver.PRE_FORTRESS_SMTLIB.id())) {
            writeSmtlibToFile(logger, options, context);
            return null;
        }

        // TODO: choose a solver based on options
        try (ModelFinder finder = createModelFinder(Z3CliInterface$.MODULE$)) {
            context.configureModelFinder(finder);
            finder.addLogger(logger);
            ModelFinderResult result = finder.checkSat();

            if (result instanceof ErrorResult) {
                throw new ErrorFatal("Fortress error: " + ((ErrorResult) result).message());
            }
            if (result == ModelFinderResult.Timeout()) {
                throw new TimeoutException();
            }

            Interpretation interpretation = (result == ModelFinderResult.Sat()) ? finder.viewModel() : null;
            return new FortressSolution(
                    interpretation, translator, context, sigs, options.originalFilename, command.toString());
        }
    }

    // TODO: configure the model finder based on the FortressOptions
    private ModelFinder createModelFinder(SolverInterface solverInterface) {
        // For now we use this compiler as a good default.
        return new CompilationModelFinder(solverInterface) {
            @Override
            public LogicCompiler createCompiler() {
                // This is abstract (accidentally?) so we just make an anonymous inner class.
                return new DatatypeMethodWithRangeCompiler() {};
            }
        };
    }

    private void translateSigs(Iterable<Sig> sigs, Translator translator, TranslationContext context) {
        // We translate sigs in the following order:
        // 1. Each top-level PrimSig; translators should translate child PrimSigs.
        // 2. All SubsetSigs, in such an order that for each SubsetSig, all of its parent SubsetSigs
        // have been translated before it is translated.

        // 1. Each top-level PrimSig. (Also count the number of subset sigs since we only have an Iterable.)
        int numSubsetSigs = 0;
        Set<String> sigNamesSeen = new HashSet<>();
        for (Sig sig : sigs) {
            if (!sig.builtin) {
                if (sig instanceof Sig.PrimSig && sig.isTopLevel()) {
                    translator.translate(sig, context);
                    sigNamesSeen.add(sig.label);
                }
                if (sig instanceof Sig.SubsetSig) {
                    numSubsetSigs++;
                }
            }
        }

        // 2. SubsetSigs, in the specified order.
        // If this becomes a performance bottleneck, consider a topological sort instead.
        boolean changed;
        int numSubsetSigsTranslated = 0;
        do {
            changed = false;
            for (Sig sig : sigs) {
                if (!sigNamesSeen.contains(sig.label) && sig instanceof Sig.SubsetSig) {
                    Sig.SubsetSig subsetSig = (Sig.SubsetSig) sig;

                    // Have all the parents been translated?
                    if (subsetSig.parents.stream().allMatch(
                            p -> p instanceof Sig.PrimSig || sigNamesSeen.contains(p.label))) {
                        translator.translate(subsetSig, context);
                        sigNamesSeen.add(sig.label);
                        numSubsetSigsTranslated++;
                        changed = true;
                    }
                }
            }
        } while (changed);

        if (numSubsetSigsTranslated != numSubsetSigs) {
            // If there's any subset sigs left, there's a cycle somewhere. Should be caught by parser.
            throw new ErrorFatal("Cyclic inheritance in subset sigs!");
        }
    }

    private void translateFields(Iterable<Sig> sigs, Translator translator, TranslationContext context) {
        // Translate every field from each sig.
        for (Sig sig : sigs) {
            for (Decl fieldDecl : sig.getFieldDecls()) {
                for (ExprHasName name : fieldDecl.names) {
                    // We pass the Field rather than the Decl because Decls appear in other locations too
                    // (such as in quantifier formulas).
                    Sig.Field field = (Sig.Field) name;
                    translator.translate(field, context);
                }
            }
        }
    }

    private void writeFortressToFile(PortusLogger logger, A4Options options, TranslationContext context)
            throws IOException {
        List<String> lines = new ArrayList<>();
        lines.add(context.getTheory().toString());
        lines.add("Bitwidth: " + context.getBitwidth());
        for (Sort sort : context.getTheory().sortsJava()) {
            lines.add("Scope of " + sort.name() + ": " + context.sortPolicy.getSortScope(sort));
        }

        File fortressFile = options.portusOptions.createOutputFile(PortusOptions.MSFOL_EXTENSION);
        Files.write(Paths.get(fortressFile.getAbsolutePath()), lines, Charset.defaultCharset());
        logger.outputFilename(fortressFile.getAbsolutePath());
    }

    private void writeSmtlibToFile(PortusLogger logger, A4Options options, TranslationContext context)
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
                    ProblemState problemState = ProblemState.apply(theory,
                            PortusUtil.<Sort, Scope>toScalaMap(context.getSortToScopeMap()));
                    try {
                        writer.write(Dump.problemStateToSmtlib(problemState));
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
                finder = createModelFinder(solverInterface);
            } else { // PRE_FORTRESS_SMTLIB
                // Use only the typechecking transformer
                finder = new CompilationModelFinder(solverInterface) {
                    @Override
                    public LogicCompiler createCompiler() {
                        ConfigurableCompiler compiler = new ConfigurableCompiler();
                        compiler.addTransformer(
                                TheoryTransformer.asProblemStateTransformer(TypecheckSanitizeTransformer$.MODULE$));
                        compiler.addTransformer(EnumEliminationTransformer$.MODULE$);
                        compiler.addTransformer(DomainEliminationTransformer$.MODULE$);
                        return compiler;
                    }
                };
            }

            context.configureModelFinder(finder);
            finder.checkSat();
            writer.flush();
        }
        logger.outputFilename(smtlibFile.getAbsolutePath());
    }

}
