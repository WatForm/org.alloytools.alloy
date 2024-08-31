package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.modelfinders.ModelFinder;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.ConstantDefinition;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import fortress.problemstate.Scope;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Represents the translation environment for a certain expression, including the
 * theory being built. Mutable, so translators can add items to the theory.
 */
final class TranslationContext {

    // The Fortress options to be used for the translation.
    public final PortusOptions options;

    // Calculates the scopes for each signature.
    public final ScopeComputer scoper;

    // In charge of assigning ranges of Fortress domain elements in sigs to sorts when necessary.
    public final RangeAssigner rangeAssigner;

    // The context used for keeping track of the mapping of Alloy variables to terms and expressions in lets.
    public final VarMappingContext varMappingContext;

    // The current theory. Mutable.
    private Theory theory;

    // The set of sorts to mark as unchanging in Fortress.
    // This should include any sort for which the Portus translation depends on the scope,
    // i.e. whenever we expand over the atoms of a sort or refer to its domain elements.
    // If a sort is unchanging then we can't mess with its scope in the output, because it no longer
    // represents the same problem.
    private final Set<Sort> unchangingSorts;

    // A set of sorts to force to have exact Fortress scopes.
    // Any sort which is not on this list can have an exact or non-exact sort depending on the scope of its
    // top-level sig, if it has a single top-level sig making it up.
    private final Set<Sort> forcedExactScopeSorts;

    // The set of sigs that are ordered with the ordering module.
    // Some optimizations (i.e., the one sig optimization) have to be disabled for children of ordered sigs.
    private final Set<Sig> orderedSigs;

    public TranslationContext(
            PortusOptions options, ScopeComputer scoper, SortPolicy sortPolicy, RangeAssigner rangeAssigner) {
        this.options = options;
        this.scoper = scoper;
        this.rangeAssigner = rangeAssigner;
        this.varMappingContext = new VarMappingContext();
        this.theory = sortPolicy.addSortsToTheory(Theory.empty());
        this.unchangingSorts = new HashSet<>();
        this.forcedExactScopeSorts = new HashSet<>();
        this.orderedSigs = new HashSet<>();
    }

    /**
     * Copy constructor: copy the context so changes to the new context don't affect the original.
     */
    public TranslationContext(TranslationContext context) {
        this.options = context.options;
        this.scoper = context.scoper;
        this.theory = context.theory; // theory is immutable
        this.rangeAssigner = new RangeAssigner(context.rangeAssigner); // deep-copy state
        this.varMappingContext = new VarMappingContext(context.varMappingContext); // deep-copy state
        this.unchangingSorts = new HashSet<>(context.unchangingSorts);
        this.forcedExactScopeSorts = new HashSet<>(context.forcedExactScopeSorts);
        this.orderedSigs = new HashSet<>(context.orderedSigs);
    }

    /**
     * Get the bitwidth used for the `Int` sort.
     */
    public int getBitwidth() {
        return scoper.getBitwidth();
    }

    /**
     * Get the maximum sequence length, i.e. the scope of the `seq/Int` sig.
     */
    public int getMaxSeq() {
        return scoper.getMaxSeq();
    }

    public void addAxiom(Term axiom) {
        theory = theory.withAxiom(axiom);
    }

    public void addConstant(AnnotatedVar constant) {
        theory = theory.withConstantDeclaration(constant);
    }

    public void addConstantDefinition(ConstantDefinition definition) {
        theory = theory.withConstantDefinition(definition);
    }

    public void addFunctionDeclaration(FuncDecl funcDecl) {
        theory = theory.withFunctionDeclaration(funcDecl);
    }

    public void addFunctionDefinition(FunctionDefinition definition) {
        theory = theory.withFunctionDefinition(definition);
    }

    /**
     * Have we added a function with the given name?
     * Useful for avoiding adding duplicate functions.
     */
    public boolean hasFunctionWithName(String name) {
        return theory.functionDeclarations().exists(func -> func.name().equals(name))
                || theory.functionDefinitions().exists(def -> def.name().equals(name));
    }

    // The following are convenience delegates to VarMappingContext.

    /**
     * Add a mapping from an Alloy variable name to a Fortress term.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addTermMapping(String alloyVarName, AnnotatedTerm fortressTerm) {
        varMappingContext.addTermMapping(alloyVarName, fortressTerm);
    }

    /**
     * Does the current lexical scope have a Fortress term associated with
     * the given Alloy variable name?
     */
    public boolean hasTermMapping(String alloyVarName) {
        return varMappingContext.hasTermMapping(alloyVarName);
    }

    /**
     * Get the Fortress term associated with an Alloy variable name in the
     * current lexical scope. Return null if there's no such associated variable.
     */
    public AnnotatedTerm getTermMapping(String alloyVarName) {
        return varMappingContext.getTermMapping(alloyVarName);
    }

    /**
     * Add a mapping from an Alloy variable name to a 'let' Alloy expression.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addLetMapping(String alloyVarName, Expr boundExpr) {
        varMappingContext.addLetMapping(alloyVarName, boundExpr);
    }

    /**
     * Add multiple let mappings at the same time such that they don't conflict.
     * Use this to map multiple let mappings such that variable references in later bound expressions with the same
     * name as earlier variable names are not mapped to those variable names.
     * For example, if you want to simultaneously map x=a and y=x, where the x in y=x is a preexisting bound var,
     * calling addLetMapping twice would result in mapping y to a (i.e. let x=a | let y=x | ...) whereas calling
     * this method results in mapping y to the original x, as desired.
     * All mappings must be removed individually with {@link #removeMapping(String)}.
     */
    public void addSimultaneousLetMappings(List<Pair<String, Expr>> varNamesAndBoundExprs) {
        varMappingContext.addSimultaneousLetMappings(varNamesAndBoundExprs);
    }

    /**
     * Does the current lexical scope have a bound expression associated with
     * the given Alloy variable name?
     */
    public boolean hasLetMapping(String alloyVarName) {
        return varMappingContext.hasLetMapping(alloyVarName);
    }

    /**
     * Get the bound expression associated with an Alloy variable name in the
     * current lexical scope. Return null if there's no such expression bound.
     */
    public VarMappingContext.LetContext getLetMapping(String alloyVarName) {
        return varMappingContext.getLetMapping(alloyVarName);
    }

    /**
     * Remove a variable or bound expression mapping for an Alloy variable name.
     * This should be done when the variable name goes out of scope.
     */
    public void removeMapping(String alloyVarName) {
        varMappingContext.removeMapping(alloyVarName);
    }

    /**
     * A helper to add let mappings for all the variables in an ExprCall.
     */
    public void addLetMappingsFromCall(ExprCall call) {
        // Add them simultaneously so they can't conflict
        varMappingContext.addLetMappingsFromCall(call);
    }

    /**
     * A helper to remove the let mappings for all the variables in an ExprCall,
     * as previously added by {@link #addLetMappingsFromCall(ExprCall)}.
     */
    public void removeLetMappingsFromCall(ExprCall call) {
        varMappingContext.removeLetMappingsFromCall(call);
    }

    /** @see VarMappingContext#addFortressVar(Var, Sort)  */
    public void addFortressVar(Var var, Sort sort) {
        varMappingContext.addFortressVar(var, sort);
    }

    /** @see VarMappingContext#addFortressVar(AnnotatedVar)  */
    public void addFortressVar(AnnotatedVar var) {
        varMappingContext.addFortressVar(var);
    }

    /** @see VarMappingContext#addFortressVars(List)  */
    public void addFortressVars(List<AnnotatedVar> vars) {
        varMappingContext.addFortressVars(vars);
    }

    /** @see VarMappingContext#addFortressVars(AnnotatedVar...)  */
    public void addFortressVars(AnnotatedVar... vars) {
        varMappingContext.addFortressVars(vars);
    }

    /** @see VarMappingContext#isFortressVarKnown(Var)  */
    public boolean isFortressVarKnown(Var var) {
        return varMappingContext.isFortressVarKnown(var);
    }

    /** @see VarMappingContext#getFortressVarSort(Var)  */
    public Sort getFortressVarSort(Var var) {
        return varMappingContext.getFortressVarSort(var);
    }

    /** @see VarMappingContext#removeFortressVar(Var)  */
    public void removeFortressVar(Var var) {
        varMappingContext.removeFortressVar(var);
    }

    /** @see VarMappingContext#removeFortressVar(AnnotatedVar)  */
    public void removeFortressVar(AnnotatedVar var) {
        varMappingContext.removeFortressVar(var);
    }

    /** @see VarMappingContext#removeFortressVars(List)  */
    public void removeFortressVars(List<AnnotatedVar> vars) {
        varMappingContext.removeFortressVars(vars);
    }

    /** @see VarMappingContext#removeFortressVars(AnnotatedVar...)  */
    public void removeFortressVars(AnnotatedVar... vars) {
        varMappingContext.removeFortressVars(vars);
    }

    /** Configure a model finder's theory and scopes to check this translation. */
    public void configureModelFinder(ModelFinder finder, SortPolicy sortPolicy) {
        finder.setTheory(theory);
        sortPolicy.configureModelFinderScopes(finder, forcedExactScopeSorts, unchangingSorts, scoper);
        // TODO - allow configuring modular vs unbounded ints?
    }

    /** Mark the sort as unchanging in the Fortress output. */
    public void markSortUnchanging(Sort sort) {
        unchangingSorts.add(sort);
    }

    public void forceSortExact(Sort sort) {
        forcedExactScopeSorts.add(sort);
    }

    public void setSigOrdered(Sig sig) {
        orderedSigs.add(sig);
    }

    public boolean isSigOrdered(Sig sig) {
        return orderedSigs.contains(sig);
    }

    /** Given a sort policy, use its information with our unchanging sort list to get the sort to scope map. */
    public Map<Sort, Scope> getSortToScopeMap(SortPolicy sortPolicy) {
        return sortPolicy.getSortToScopeMap(forcedExactScopeSorts, unchangingSorts, scoper);
    }

    /**
     * Get the theory being built. This is for debugging and visibility; for solving prefer
     * {@link #configureModelFinder(ModelFinder, SortPolicy)}.
     */
    public Theory getTheory() {
        return theory;
    }

}
