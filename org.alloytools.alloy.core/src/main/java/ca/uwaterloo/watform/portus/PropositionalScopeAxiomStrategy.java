package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.DomainElement;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * Express scope axioms using Z3's cardinality and pseudo-Boolean cardinality operators:
 * https://microsoft.github.io/z3guide/docs/logic/propositional-logic
 * Compatible only with Z3!
 */
final class PropositionalScopeAxiomStrategy implements ScopeAxiomStrategy {

    private final SortPolicy sortPolicy;

    public PropositionalScopeAxiomStrategy(SortPolicy sortPolicy) {
        this.sortPolicy = sortPolicy;
    }

    @Override
    public Term makeExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        System.out.println("PROPOSITIONAL EXACT: " + sig + " @ " + scope);
        return makeExactlyK(scope, makeDEInSigList(sig, recursiveTranslator, context));
    }

    @Override
    public Term makeNonExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        System.out.println("PROPOSITIONAL NON EXACT: " + sig + " @ " + scope);
        return makeAtMostK(scope, makeDEInSigList(sig, recursiveTranslator, context));
    }

    private List<Term> makeDEInSigList(Sig sig, Translator recursiveTranslator, TranslationContext context) {
        Sort sort = sortPolicy.getSort(sig);
        int sortScope = sortPolicy.getSortScope(sort);

        List<Term> terms = new ArrayList<>(sortScope);
        for (int i = 1; i <= sortScope; i++) {
            DomainElement de = Term.mkDomainElement(i, sort);
            terms.add(makeDEInSig(de, sig, recursiveTranslator, context));
        }
        return terms;
    }

    private Term makeDEInSig(DomainElement de, Sig sig, Translator recursiveTranslator, TranslationContext context) {
        return recursiveTranslator.translate(ExprElementOf.make(new AnnotatedTerm(de, de.sort()), sig), context);
    }

    private Term makeAtMostK(int k, List<Term> args) {
        String smtlib = "(_ at-most " + k + ")";
        return Term.mkCustomPred(smtlib, args);
    }

    private Term makeExactlyK(int k, List<Term> args) {
        StringBuilder smtlib = new StringBuilder("(_ pbeq " + k);
        for (int i = 0; i < args.size(); i++) {
            smtlib.append(" 1");
        }
        smtlib.append(")");
        return Term.mkCustomPred(smtlib.toString(), args);
    }

}
