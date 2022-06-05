package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfind.ModelFinder;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;

/**
 * Represents the translation environment for a certain expression, including the
 * theory being built. Mutable, so translators can add items to the theory.
 */
final class TranslationContext {

    // The Fortress options to be used for the translation.
    public final FortressOptions options;

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

    // The current lexical scope's mapping from Alloy variable labels to either
    // Fortress Vars or Alloy expressions as used in the "let x = e | ..." construct.
    // We use a single Env so these types of mappings can shadow each other.
    private final Env<String, Either<Var, Expr>> alloyVarMapping;

    public TranslationContext(FortressOptions options, A4Reporter reporter, ScopeComputer scoper) {
        this.options = options;
        this.reporter = (reporter == null) ? A4Reporter.NOP : reporter;
        this.scoper = scoper;
        this.alloyVarMapping = new Env<>();
    }

    // Copy constructor: copy the context so changes to the new context don't affect the original.
    public TranslationContext(TranslationContext context) {
        this.options = context.options;
        this.reporter = context.reporter;
        this.scoper = context.scoper;
        this.theory = context.theory; // theory is immutable
        this.totalScope = context.totalScope;
        this.alloyVarMapping = context.alloyVarMapping.dup();
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
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addVarMapping(String alloyVarName, Var fortressVar) {
        alloyVarMapping.put(alloyVarName, Either.asFirst(fortressVar));
    }

    /**
     * Does the current lexical scope have a Fortress variable associated with
     * the given Alloy variable name?
     */
    public boolean hasVarMapping(String alloyVarName) {
        return alloyVarMapping.has(alloyVarName) && alloyVarMapping.get(alloyVarName).hasFirst();
    }

    /**
     * Get the Fortress variable associated with an Alloy variable name in the
     * current lexical scope. Return null if there's no such associated variable.
     */
    public Var getVarMapping(String alloyVarName) {
        if (hasVarMapping(alloyVarName)) {
            return alloyVarMapping.get(alloyVarName).getFirst();
        }
        return null;
    }

    /**
     * Add a mapping from an Alloy variable name to a bound expression.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addLetMapping(String alloyVarName, Expr boundExpr) {
        alloyVarMapping.put(alloyVarName, Either.asSecond(boundExpr));
    }

    /**
     * Does the current lexical scope have a bound expression associated with
     * the given Alloy variable name?
     */
    public boolean hasLetMapping(String alloyVarName) {
        return alloyVarMapping.has(alloyVarName) && alloyVarMapping.get(alloyVarName).hasSecond();
    }

    /**
     * Get the bound expression associated with an Alloy variable name in the
     * current lexical scope. Return null if there's no such expression bound.
     */
    public Expr getLetMapping(String alloyVarName) {
        if (hasLetMapping(alloyVarName)) {
            return alloyVarMapping.get(alloyVarName).getSecond();
        }
        return null;
    }

    /**
     * Remove a variable or bound expression mapping for an Alloy variable name.
     * This should be done when the variable name goes out of scope.
     */
    public void removeMapping(String alloyVarName) {
        alloyVarMapping.remove(alloyVarName);
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
