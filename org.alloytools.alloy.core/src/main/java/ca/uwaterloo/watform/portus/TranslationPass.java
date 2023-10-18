package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * The main pass which actually performs the translation.
 */
final class TranslationPass implements Pass {

    private final Translator translator;
    private final SortPolicy sortPolicy;
    private final SigAxioms sigAxioms;

    public TranslationPass(Translator translator, SortPolicy sortPolicy, SigAxioms sigAxioms) {
        this.translator = translator;
        this.sortPolicy = sortPolicy;
        this.sigAxioms = sigAxioms;
    }

    @Override
    public void performPass(Iterable<Sig> sigs, Command command, ScopeComputer scoper, TranslationContext context) {
        // Do sigs first, then fields, then the formula.
        // We have to do fields after sigs because a field can refer to sigs that come after it.
        translateSigs(sigs, context);
        translateFields(sigs, context);

        // Translate all the facts now, since they could refer to sigs or fields.
        translateSigFacts(sigs, context);

        // Add extra axioms: the top level sigs are disjoint.
        addDisjointnessAxioms(sigs, context);

        // Translate the entire formula.
        context.addAxiom(translator.translate(command.formula, context));
    }

    private void translateSigs(Iterable<Sig> sigs, TranslationContext context) {
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

    private void translateFields(Iterable<Sig> sigs, TranslationContext context) {
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

    private void translateSigFacts(Iterable<Sig> sigs, TranslationContext context) {
        // Translate all the facts from each sig.
        for (Sig sig : sigs) {
            for (Expr fact : sig.getFacts()) {
                Expr quantifiedFact;
                if (sig.isOne == null) {
                    // non-one sigs: equivalent to "all this: Sig | fact"
                    quantifiedFact = fact.forAll(sig.decl);
                } else {
                    // one sigs: optimize to "let this=Sig | fact"
                    quantifiedFact = ExprLet.make(null, (ExprVar) sig.decl.get(), sig, fact);
                }
                context.addAxiom(translator.translate(quantifiedFact, context));
            }
        }
    }

    private void addDisjointnessAxioms(Iterable<Sig> sigs, TranslationContext context) {
        // Add axioms asserting that the top-level sigs in each sort are disjoint
        for (Sort sort : context.getTheory().sortsJava()) {
            List<Sig> sortTLSigs = StreamSupport.stream(sigs.spliterator(), false)
                    // Ignore String for now, we don't support it - TODO support Sig.STRING
                    .filter(sig -> sig != Sig.STRING)
                    .filter(sig -> sig.isTopLevel() && Objects.equals(sortPolicy.getSort(sig), sort))
                    .collect(Collectors.toList());

            // all the sigs are pairwise disjoint
            sigAxioms.assertSigsPairwiseDisjoint(sortTLSigs, context);
        }
    }

}
