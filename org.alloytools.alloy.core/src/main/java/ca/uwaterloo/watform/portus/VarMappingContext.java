package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;

/**
 * Responsible for keeping track of the current Alloy lexical scope's mapping from Alloy variables to Fortress Terms
 * (e.g. from quantifiers) and Alloy expressions (e.g. from lets).
 */
public final class VarMappingContext {

    // The current Alloy lexical scope's mapping from Alloy variable labels to either
    // Fortress Terms (i.e. for quantified vars) or Alloy expressions as used in the "let x = e | ..." construct.
    // We use a single Env so these types of mappings can shadow each other.
    private Env<String, Either<AnnotatedTerm, LetContext>> alloyVarMapping;

    // The current Fortress translation scope's map from Fortress variables to their corresponding sorts.
    // This is necessary because Fortress does not keep track of the sorts of its variables itself.
    private final Env<Var, Sort> fortressVarsToSorts;

    public VarMappingContext() {
        this.alloyVarMapping = new Env<>();
        this.fortressVarsToSorts = new Env<>();
    }

    public VarMappingContext(VarMappingContext varMappingContext) {
        this.alloyVarMapping = varMappingContext.alloyVarMapping.dup();
        this.fortressVarsToSorts = varMappingContext.fortressVarsToSorts.dup();
    }

    /**
     * Add a mapping from an Alloy variable name to a Fortress term.
     * The mapping should be valid for the current lexical scope and be removed at the end
     * of the scope with {@link #removeMapping(String)}.
     */
    public void addTermMapping(String alloyVarName, AnnotatedTerm fortressTerm) {
        alloyVarMapping.put(alloyVarName, Either.asFirst(fortressTerm));
    }

    /**
     * Does the current lexical scope have a Fortress term associated with
     * the given Alloy variable name?
     */
    public boolean hasTermMapping(String alloyVarName) {
        return alloyVarMapping.has(alloyVarName) && alloyVarMapping.get(alloyVarName).hasFirst();
    }

    /**
     * Get the Fortress term associated with an Alloy variable name in the
     * current lexical scope. Return null if there's no such associated variable.
     */
    public AnnotatedTerm getTermMapping(String alloyVarName) {
        if (hasTermMapping(alloyVarName)) {
            return alloyVarMapping.get(alloyVarName).getFirst();
        }
        return null;
    }

    /**
     * Add a mapping from an Alloy variable name to a 'let' Alloy expression.
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
        Env<String, Either<AnnotatedTerm, LetContext>> oldAlloyVarMapping = alloyVarMapping.dup();
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

    /**
     * Add a mapping for the sort of a Fortress variable.
     * This must be called before translating any term for which the variable will be in scope, and the mapping must
     * be removed afterwards with {@link #removeFortressVar}.
     */
    public void addFortressVar(Var var, Sort sort) {
        fortressVarsToSorts.put(var, sort);
    }

    public void addFortressVar(AnnotatedVar var) {
        addFortressVar(var.variable(), var.sort());
    }

    public void addFortressVars(List<AnnotatedVar> vars) {
        for (AnnotatedVar var : vars) {
            addFortressVar(var);
        }
    }

    public void addFortressVars(AnnotatedVar... vars) {
        addFortressVars(Arrays.asList(vars));
    }

    /**
     * Is the Fortress variable in scope?
     */
    public boolean isFortressVarKnown(Var var) {
        return fortressVarsToSorts.has(var);
    }

    /**
     * Get the sort for the Fortress variable, if it is in scope.
     * If not, return null.
     */
    public Sort getFortressVarSort(Var var) {
        if (isFortressVarKnown(var)) {
            return fortressVarsToSorts.get(var);
        }
        return null;
    }

    /**
     * Remove the Fortress variable from the scope.
     * This must be called after translating the term in which the variable is in scope.
     */
    public void removeFortressVar(Var var) {
        fortressVarsToSorts.remove(var);
    }

    /** Convenience: remove through an AnnotatedVar. */
    public void removeFortressVar(AnnotatedVar var) {
        removeFortressVar(var.variable());
    }

    /** Remove a list of variables previously added with addFortressVars. */
    public void removeFortressVars(List<AnnotatedVar> vars) {
        // Remove in reverse order just in case, although it should be fine
        for (int i = vars.size() - 1; i >= 0; i--) {
            removeFortressVar(vars.get(i));
        }
    }

    public void removeFortressVars(AnnotatedVar... vars) {
        removeFortressVars(Arrays.asList(vars));
    }

    /** Replace all instances of sort "from" with sort "to", useful if sorts have been semantically merged. */
    public void replaceSort(Sort from, Sort to) {
        mapEnv(alloyVarMapping, either -> replaceSortInEither(either, from, to));
        mapEnv(fortressVarsToSorts, sort -> sort.equals(from) ? to : sort);
    }

    private static <K, V> void mapEnv(Env<K, V> env, Function<V, V> map) {
        Set<K> keys = new HashSet<>(env.keySet());
        Stack<V> stack = new Stack<>();

        for (K key : keys) {
            // Env acts as a stack: remove everything from env and push it onto a temp stack
            while (env.has(key)) {
                V value = env.get(key);
                env.remove(key);
                stack.push(map.apply(value));
            }

            // Now put the stack back into the env.
            while (!stack.empty()) {
                env.put(key, stack.pop());
            }
        }
    }

    private static Either<AnnotatedTerm, LetContext> replaceSortInEither(
            Either<AnnotatedTerm, LetContext> either, Sort from, Sort to) {
        if (either.hasFirst()) {
            AnnotatedTerm term = either.getFirst();
            if (Objects.equals(term.getSort(), from)) {
                term = new AnnotatedTerm(term.getTerm(), to);
            }
            return Either.asFirst(term);
        } else { // either.hasSecond()
            LetContext context = either.getSecond();
            context.replaceSort(from, to);
            return Either.asSecond(context);
        }
    }

    /**
     * Drop all let-mappings. Term mappings are kept intact.
     * For use when lets have been expanded but term mappings are still important.
     */
    public void dropAllLets() {
        Set<String> keys = new HashSet<>(alloyVarMapping.keySet());
        Stack<AnnotatedTerm> termMappings = new Stack<>();
        for (String key : keys) {
            // Pop the env stack
            while (alloyVarMapping.has(key)) {
                if (hasTermMapping(key)) {
                    // preserve the term mapping
                    termMappings.push(getTermMapping(key));
                }
                removeMapping(key);
            }

            // Now put the term mappings back
            while (!termMappings.empty()) {
                addTermMapping(key, termMappings.pop());
            }
        }
    }

    /**
     * Represents the expression that an ExprVar is mapped to in "let" or a function/predicate call, as well as
     * some metadata.
     */
    static final class LetContext {
        /**
         * The expression a variable is mapped to in this "let".
         */
        private final Expr expr;

        /**
         * The mapping of Alloy variable names to Fortress terms or Alloy let exprs at the place "let" appears.
         */
        private final Env<String, Either<AnnotatedTerm, LetContext>> savedVarMapping;

        /**
         * The old Alloy variable name to Fortress var/let mapping when using useLetMapping().
         */
        private Env<String, Either<AnnotatedTerm, LetContext>> oldMapping = null;

        /**
         * The TranslationContext whose mapping we've changed with useLetMapping().
         */
        private VarMappingContext mappedContext = null;

        private LetContext(Expr expr, Env<String, Either<AnnotatedTerm, LetContext>> alloyVarMapping) {
            this.expr = expr;
            this.savedVarMapping = alloyVarMapping;
        }

        /**
         * Retrieve the expression mapped in this "let".
         */
        public Expr getExpr() {
            return expr;
        }

        /**
         * Change the VarMappingContext to use the old Alloy variable to Fortress var/let mapping which was in
         * use at the time that this "let" was processed. Cannot be nested. Called {@link #resetMapping()} when done.
         * Use this to translate {@link #getExpr()} in the correct context.
         */
        public void useLetMapping(VarMappingContext context) {
            if (oldMapping != null) {
                throw new ErrorFatal("Internal Portus error: nested useLetMapping()");
            }
            oldMapping = context.alloyVarMapping;
            context.alloyVarMapping = savedVarMapping;
            mappedContext = context;
        }

        /** Convenience: change the VarMappingContext of the passed-in TranslationContext. */
        public void useLetMapping(TranslationContext context) {
            useLetMapping(context.varMappingContext);
        }

        /**
         * Reset the TranslationContext previously passed to {@link #useLetMapping(VarMappingContext)} to use the
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

        private boolean replacingSort = false;

        private void replaceSort(Sort from, Sort to) {
            // Hack: avoid reentrancy since this data structure could be cyclic
            if (replacingSort) {
                return;
            }
            replacingSort = true;

            mapEnv(savedVarMapping, either -> replaceSortInEither(either, from, to));
            if (oldMapping != null) {
                mapEnv(oldMapping,  either -> replaceSortInEither(either, from, to));
            }

            replacingSort = false;
        }
    }

}