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

    // The current theory. Mutable.
    private Theory theory = Theory.empty();

    // Scopes for each sort.
    // Invariant: the sorts in the theory are exactly the keys of the scopes map.
    private final Map<Sort, Integer> scopes = new HashMap<>();

    // The sort that members of each sig are mapped to.
    private final Map<Sig, Sort> sigsToSorts = new HashMap<>();

    // The current lexical scope's mapping from variable labels to Fortress Vars.
    private final Env<String, Var> varMapping = new Env<>();

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

    /** Set the sort that members of this sig belong to. */
    public void setSigSort(Sig sig, Sort sort) {
        sigsToSorts.put(sig, sort);
    }

    /** Get the sort that members of this sig belong to, or null if not set. */
    public Sort getSigSort(Sig sig) {
        return sigsToSorts.get(sig);
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
        for (Sort sort : theory.sortsJava()) {
            finder.setAnalysisScope(sort, scopes.get(sort));
        }
    }

    /**
     * Get the theory being built. This is mainly for testing; for production use prefer
     * {@link #configureModelFinder(ModelFinder)}.
     */
    Theory getTheory() {
        return theory;
    }

    /**
     * Get the registered scope of the given sort. Again, mainly for testing.
     * Returns a boxed Integer so that we return null if the sort doesn't have a registered scope.
     */
    Integer getSortScope(Sort sort) {
        return scopes.get(sort);
    }

}
