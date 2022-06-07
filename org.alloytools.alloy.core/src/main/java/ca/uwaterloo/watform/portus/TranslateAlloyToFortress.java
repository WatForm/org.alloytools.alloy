package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.interpretation.Interpretation;
import fortress.modelfind.ModelFinder;
import fortress.modelfind.ModelFinderResult;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

/**
 * The public API for Portus. Translate an Alloy AST to a Fortress theory, then attempt
 * to solve it using Fortress.
 */
public final class TranslateAlloyToFortress implements CommandRunner {

    @Override
    public AlloySolution executeCommand(
            A4Reporter reporter, Iterable<Sig> sigs, Command command, A4Options options) {
        ScopeComputer scoper = ScopeComputer.compute(reporter, options, sigs, command).b;

        try {
            // Actually execute the command, and time it.
            long beginTimeMs = System.currentTimeMillis();
            AlloySolution solution = executeCommand(reporter, sigs, command, scoper, options);
            long solvingTimeMs = System.currentTimeMillis() - beginTimeMs;

            reportResult(solution, reporter, command, solvingTimeMs);
            return solution;
        } catch (IOException e) {
            throw new ErrorFatal("IOException in Fortress translation", e);
        } catch (Throwable e) {
            // Alloy will catch it anyways, so rethrow as ErrorFatal for a more helpful debug message.
            throw new ErrorFatal(e.getMessage(), e);
        }
    }

    private void reportResult(
            AlloySolution solution, A4Reporter reporter, Command command, long solvingTimeMs) {
        if (solution.satisfiable()) {
            reporter.resultSAT(command, solvingTimeMs, solution);
        } else {
            reporter.resultUNSAT(command, solvingTimeMs, solution);
        }
    }

    // Execute the command specified by command, mutating and returning solution.
    private AlloySolution executeCommand(
            A4Reporter reporter, Iterable<Sig> sigs, Command command,
            ScopeComputer scoper, A4Options options) throws IOException {
        Translator translator = new TranslatorManager(options.fortressOptions);
        TranslationContext context = new TranslationContext(options.fortressOptions, reporter, scoper);

        // Do sigs first, then fields, then the formula.
        // We have to do fields after sigs because a field can refer to sigs that come after it.
        translateSigs(sigs, translator, context);
        translateFields(sigs, translator, context);
        // TODO: append all the facts and field facts to the formula (copy/abstract makeFacts)
        context.addAxiom(translator.translate(command.formula, context));

        // TODO: choose a solver based on options
        try (ModelFinder finder = ModelFinder.createDefault()) {
            context.configureModelFinder(finder);
            ModelFinderResult result = finder.checkSat();
            reporter.debug("SMT result: " + result);

            Interpretation interpretation = (result == ModelFinderResult.Sat()) ? finder.viewModel() : null;
            return new FortressSolution(
                    interpretation, translator, context, sigs, options.originalFilename, command.toString());
        }
    }

    private void translateSigs(Iterable<Sig> sigs, Translator translator, TranslationContext context) {
        // We translate sigs in the following order:
        // 1. Each top-level PrimSig; translators should translate child PrimSigs.
        // 2. All SubsetSigs, in such an order that for each SubsetSig, all of its parent SubsetSigs
        // have been translated before it is translated.

        // 1. Each top-level PrimSig. (Also count the number of sigs since we only have an Iterable.)
        int numSigs = 0;
        Set<String> sigNamesSeen = new HashSet<>();
        for (Sig sig : sigs) {
            if (!sig.builtin) {
                if (sig instanceof Sig.PrimSig && sig.isTopLevel()) {
                    translator.translate(sig, context);
                    sigNamesSeen.add(sig.label);
                }
                numSigs++;
            }
        }

        // 2. SubsetSigs, in the specified order.
        // If this becomes a performance bottleneck, consider a topological sort instead.
        boolean changed;
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
                        changed = true;
                    }
                }
            }
        } while (changed);

        if (sigNamesSeen.size() != numSigs) {
            // If there's anything left, there's a cycle somewhere. Should be caught by parser.
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

}
