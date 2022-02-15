package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfind.ModelFinder;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents the translation environment for a certain expression, including the
 * theory being built. Mutable, so translators can add items to the theory.
 */
// TODO: I'd prefer to make this immutable...
final class TranslationContext {

    // A reporter that translators can use to log output.
    public final A4Reporter reporter;

    // Calculates the scopes for each signature.
    public final ScopeComputer scoper;

    // The current theory. Mutable.
    private Theory theory = Theory.empty();

    // Invariant: the sorts in the theory are exactly the keys of the scopes map.
    private final Map<Sort, Integer> scopes = new HashMap<>();

    public TranslationContext(A4Reporter reporter, ScopeComputer scoper) {
        this.reporter = (reporter == null) ? A4Reporter.NOP : reporter;
        this.scoper = scoper;
    }

    public void addAxiom(Term axiom) {
        theory = theory.withAxiom(axiom);
    }

    public void addSort(Sort sort, int scope) {
        // keep the scope map in sync with the theory
        scopes.put(sort, scope);
        theory = theory.withSort(sort);
    }

    public void addConstant(AnnotatedVar constant) {
        theory = theory.withConstant(constant);
    }

    public void addFunctionDeclaration(FuncDecl funcDecl) {
        theory = theory.withFunctionDeclaration(funcDecl);
    }

    /** Configure a model finder's theory and scopes to check this translation. */
    public void configureModelFinder(ModelFinder finder) {
        finder.setTheory(theory);
        for (Sort sort : theory.sortsJava()) {
            finder.setAnalysisScope(sort, scopes.get(sort));
        }
    }

}
