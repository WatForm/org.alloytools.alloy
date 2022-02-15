package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfind.ModelFinder;
import fortress.modelfind.ModelFinderResult;
import fortress.msfol.Sort;

import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The public API for Portus. Translate an Alloy AST to a Fortress theory, then attempt
 * to solve it using Fortress.
 */
public final class TranslateAlloyToFortress {

    public void executeCommand(
            A4Reporter reporter, List<Sig> sigs, Command command,
            ScopeComputer scoper, FortressOptions options) throws IOException {
        Translator translator = new TranslatorManager(options);
        TranslationContext context = new TranslationContext(reporter, scoper);

        // Do sigs first, then the formula.
        translateSigs(sigs, translator, context);
        // TODO: append all the facts and field facts to the formula (copy/abstract makeFacts)
        context.addAxiom(translator.translate(command.formula, context));

        // TODO: choose a solver based on options
        try (ModelFinder finder = ModelFinder.createDefault()) {
            context.configureModelFinder(finder);
            ModelFinderResult result = finder.checkSat();
            reporter.debug("SMT result: " + result);
        }

        // TODO: return a result to hook into Alloy
    }

    private void translateSigs(List<Sig> sigs, Translator translator, TranslationContext context) {
        // We translate sigs in the following order:
        // 1. Each top-level PrimSig; translators should translate child PrimSigs.
        // 2. All SubsetSigs, in such an order that for each SubsetSig, all of its parent SubsetSigs
        // have been translated before it is translated.
        Set<String> sigNamesSeen = new HashSet<>();

        // 1. PrimSig trees. TODO actually translate PrimSig trees
        for (Sig sig : sigs) {
            // TODO: can this be UNIV or other built-in sigs?
            if (sig instanceof Sig.PrimSig && sig.isTopLevel()) {
                translatePrimSigTree((Sig.PrimSig) sig, sigNamesSeen, translator, context);
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
                    if (subsetSig.parents.stream().allMatch(p -> sigNamesSeen.contains(p.label))) {
                        translator.translate(subsetSig, context);
                        sigNamesSeen.add(sig.label);
                        changed = true;
                    }
                }
            }
        } while (changed);

        if (sigNamesSeen.size() != sigs.size()) {
            // If there's anything left, there's a cycle somewhere. Should be caught by parser.
            throw new ErrorFatal("Cyclic inheritance in subset sigs!");
        }
    }

    private void translatePrimSigTree(
            Sig.PrimSig sig, Set<String> sigNamesSeen, Translator translator, TranslationContext context) {
        if (sigNamesSeen.contains(sig.label)) {
            throw new ErrorFatal("Cyclic inheritance!"); // should be caught by parser
        }
        sigNamesSeen.add(sig.label);

        // Pre-order: translate the sig before its children.
        translator.translate(sig, context);
        for (Sig.PrimSig child : sig.children()) {
            translatePrimSigTree(sig, sigNamesSeen, translator, context);
        }
    }

}
