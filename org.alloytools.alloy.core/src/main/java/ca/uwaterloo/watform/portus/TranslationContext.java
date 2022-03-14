package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfind.ModelFinder;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents the translation environment for a certain expression, including the
 * theory being built. Mutable, so translators can add items to the theory.
 */
final class TranslationContext {

    // A reporter that translators can use to log output.
    public final A4Reporter reporter;

    // Calculates the scopes for each signature.
    public final ScopeComputer scoper;

    // The single universal sort.
    public final Sort univSort = Sort.mkSortConst("univ");

    // The current theory. Mutable.
    private Theory theory = Theory.empty().withSort(univSort);

    // The scope needed for the universal sort.
    // This should be the sum of the scopes of all top-level sorts.
    private int totalScope = 0;

    // The current lexical scope's mapping from variable labels to Fortress Vars.
    private final Env<String, Var> varMapping = new Env<>();

    public TranslationContext(A4Reporter reporter, ScopeComputer scoper) {
        this.reporter = (reporter == null) ? A4Reporter.NOP : reporter;
        this.scoper = scoper;
    }

    // Add to the total scope needed for the universal sort.
    // This should be called for each top-level sig.
    public void addToUnivScope(int scope) {
        totalScope += scope;
    }

    public void addAxiom(Term axiom) {
        theory = theory.withAxiom(axiom);
    }

    public void addConstant(AnnotatedVar constant) {
        theory = theory.withConstant(constant);
    }

    public void addFunctionDeclaration(FuncDecl funcDecl) {
        theory = theory.withFunctionDeclaration(funcDecl);
    }

    /**
     * Add a mapping from an Alloy variable name to a Fortress variable.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeVarMapping(String)}
     */
    public void addVarMapping(String alloyVarName, Var fortressVar) {
        varMapping.put(alloyVarName, fortressVar);
    }

    /**
     * Remove a variable mapping for an Alloy variable name.
     * This should be done when the variable name goes out of scope.
     */
    public void removeVarMapping(String alloyVarName) {
        varMapping.remove(alloyVarName);
    }

    /**
     * Does the current lexical scope have a Fortress variable associated with
     * the given Alloy variable name?
     */
    public boolean hasVarMapping(String alloyVarName) {
        return varMapping.has(alloyVarName);
    }

    /**
     * Get the Fortress variable associated with an Alloy variable name in the
     * current lexical scope.
     */
    public Var getVarMapping(String alloyVarName) {
        return varMapping.get(alloyVarName);
    }

    /** Configure a model finder's theory and scopes to check this translation. */
    public void configureModelFinder(ModelFinder finder) {
        finder.setTheory(theory);
        // Make sure the sort is non-empty, even if there are no sigs in the model
        finder.setAnalysisScope(univSort, Math.min(totalScope, 1));
    }

    /**
     * Get the theory being built. This is for testing; for production use prefer
     * {@link #configureModelFinder(ModelFinder)}.
     */
    Theory getTheory() {
        return theory;
    }

    /**
     * Get the total scope (i.e. the scope of the univ sort). This is for testing;
     * for production use prefer {@link #configureModelFinder(ModelFinder)}.
     */
    int getTotalScope() {
        return totalScope;
    }

}
