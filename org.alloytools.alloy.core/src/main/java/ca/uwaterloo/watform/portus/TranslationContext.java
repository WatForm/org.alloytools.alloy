package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import fortress.modelfind.ModelFinder;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.problemstate.Scope;
import scala.collection.Set$;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Represents the translation environment for a certain expression, including the
 * theory being built. Mutable, so translators can add items to the theory.
 */
final class TranslationContext {

    /**
     * Represents the expression that an ExprVar is mapped to in "let" or a function/predicate call, as well as
     * some metadata.
     */
    static final class LetContext {
        /** The expression a variable is mapped to in this "let". */
        private final Expr expr;

        /** The mapping of Alloy variable names to Fortress vars/lets at the place this "let" appears. */
        private final Env<String, Either<AnnotatedVar, LetContext>> savedVarMapping;

        /** The old Alloy variable name to Fortress var/let mapping when using useLetMapping(). */
        private Env<String, Either<AnnotatedVar, LetContext>> oldMapping = null;

        /** The TranslationContext whose mapping we've changed with useLetMapping(). */
        private TranslationContext mappedContext = null;

        private LetContext(Expr expr, Env<String, Either<AnnotatedVar, LetContext>> alloyVarMapping) {
            this.expr = expr;
            this.savedVarMapping = alloyVarMapping;
        }

        /** Retrieve the expression mapped in this "let". */
        public Expr getExpr() {
            return expr;
        }

        /**
         * Change the TranslationContext to use the old Alloy variable to Fortress var/let mapping which was in
         * use at the time that this "let" was processed. Cannot be nested. Called {@link #resetMapping()} when done.
         * Use this to translate {@link #getExpr()} in the correct context.
         */
        public void useLetMapping(TranslationContext context) {
            if (oldMapping != null) {
                throw new ErrorFatal("Internal Portus error: nested useLetMapping()");
            }
            oldMapping = context.alloyVarMapping;
            context.alloyVarMapping = savedVarMapping;
            mappedContext = context;
        }

        /**
         * Reset the TranslationContext previously passed to {@link #useLetMapping(TranslationContext)} to use the
         * proper Alloy variable to Fortress var/let mapping. Must be called after useLetMapping.
         */
        public void resetMapping() {
            if (oldMapping == null) {
                throw new ErrorFatal("Internal Portus error: resetMapping() without useLetMapping()");
            }
            assert mappedContext != null;
            mappedContext.alloyVarMapping = oldMapping;
            oldMapping = null;
            mappedContext = null;
        }
    }

    // The Fortress options to be used for the translation.
    public final PortusOptions options;

    // Calculates the scopes for each signature.
    public final ScopeComputer scoper;

    // The policy for how we should assign Alloy sigs to Fortress sorts.
    public final SortPolicy sortPolicy;

    // Conveniently generate globally (to this context) unique names.
    public final NameGenerator nameGenerator;

    // The current theory. Mutable.
    private Theory theory;

    // The current lexical scope's mapping from Alloy variable labels to either
    // Fortress Vars or Alloy expressions as used in the "let x = e | ..." construct.
    // We use a single Env so these types of mappings can shadow each other.
    private Env<String, Either<AnnotatedVar, LetContext>> alloyVarMapping;

    // The list of sorts to mark as unchanging in Fortress.
    // This should include any sort for which the Portus translation depends on the scope,
    // i.e. whenever we expand over the atoms of a sort or refer to its domain elements.
    // If a sort is unchanging then we can't mess with its scope in the output, because it no longer
    // represents the same problem.
    private final Set<Sort> unchangingSorts;

    public TranslationContext(PortusOptions options, ScopeComputer scoper, SortPolicy sortPolicy) {
        this.options = options;
        this.scoper = scoper;
        this.sortPolicy = sortPolicy;
        this.alloyVarMapping = new Env<>();
        this.theory = sortPolicy.addSortsToTheory(Theory.empty());
        this.nameGenerator = new IntSuffixNameGenerator(
                (scala.collection.immutable.Set<String>) Set$.MODULE$.empty(), 0);
        this.unchangingSorts = new HashSet<>();
    }

    /**
     * Copy constructor: copy the context so changes to the new context don't affect the original.
     * Note: the unique name generator will be shared, so names generated by the original and the new context's name
     * generators will be distinct (and in this sense the original's name-generator state will be modified).
     */
    public TranslationContext(TranslationContext context) {
        this.options = context.options;
        this.scoper = context.scoper;
        this.theory = context.theory; // theory is immutable
        this.sortPolicy = context.sortPolicy;
        this.alloyVarMapping = context.alloyVarMapping.dup();
        this.nameGenerator = context.nameGenerator;
        this.unchangingSorts = new HashSet<>(context.unchangingSorts);
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
        theory = theory.withConstant(constant);
    }

    public void addFunctionDeclaration(FuncDecl funcDecl) {
        theory = theory.withFunctionDeclaration(funcDecl);
    }

    /**
     * Have we added a function with the given name?
     * Useful for avoiding adding duplicate functions.
     */
    public boolean hasFunctionWithName(String name) {
        return theory.functionDeclarations().exists(func -> func.name().equals(name));
    }

    /**
     * Add a mapping from an Alloy variable name to a Fortress variable.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addVarMapping(String alloyVarName, AnnotatedVar fortressVar) {
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
    public AnnotatedVar getVarMapping(String alloyVarName) {
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
        alloyVarMapping.put(alloyVarName, Either.asSecond(new LetContext(boundExpr, alloyVarMapping.dup())));
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
        Env<String, Either<AnnotatedVar, LetContext>> oldAlloyVarMapping = alloyVarMapping.dup();
        for (Pair<String, Expr> varNameAndBoundExpr : varNamesAndBoundExprs) {
            LetContext letContext = new LetContext(varNameAndBoundExpr.b, oldAlloyVarMapping);
            alloyVarMapping.put(varNameAndBoundExpr.a, Either.asSecond(letContext));
        }
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
    public LetContext getLetMapping(String alloyVarName) {
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

    /**
     * A helper to add let mappings for all the variables in an ExprCall.
     */
    public void addLetMappingsFromCall(ExprCall call) {
        // Add them simultaneously so they can't conflict
        List<Pair<String, Expr>> varNamesAndBoundExprs = new ArrayList<>();
        for (int i = 0; i < call.fun.count(); i++) {
            Expr arg = call.args.get(i);
            ExprVar param = call.fun.get(i);
            varNamesAndBoundExprs.add(new Pair<>(param.label, arg));
        }
        addSimultaneousLetMappings(varNamesAndBoundExprs);
    }

    /**
     * A helper to remove the let mappings for all the variables in an ExprCall,
     * as previously added by {@link #addLetMappingsFromCall(ExprCall)}.
     */
    public void removeLetMappingsFromCall(ExprCall call) {
        // Remove them individually, it's fine
        for (int i = 0; i < call.fun.count(); i++) {
            ExprVar param = call.fun.get(i);
            removeMapping(param.label);
        }
    }

    /** Configure a model finder's theory and scopes to check this translation. */
    public void configureModelFinder(ModelFinder finder) {
        finder.setTheory(theory);
        sortPolicy.configureModelFinderScopes(finder, unchangingSorts);
        // TODO - allow configuring modular vs unbounded ints?
    }

    /** Mark the sort as unchanging in the Fortress output. */
    public void markSortUnchanging(Sort sort) {
        unchangingSorts.add(sort);
    }

    public Map<Sort, Scope> getSortToScopeMap() {
        return sortPolicy.getSortToScopeMap(unchangingSorts);
    }

    /**
     * Get the theory being built. This is for debugging and visibility; for solving prefer
     * {@link #configureModelFinder(ModelFinder)}.
     */
    public Theory getTheory() {
        return theory;
    }

}
