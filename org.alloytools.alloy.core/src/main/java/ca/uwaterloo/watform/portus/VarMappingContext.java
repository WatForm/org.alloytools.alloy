package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.Sort;

import java.util.ArrayList;
import java.util.List;

/**
 * Responsible for keeping track of the current lexical scope's mapping from Alloy variables to Fortress Terms
 * (e.g. from quantifiers) and Alloy expressions (e.g. from lets).
 */
final class VarMappingContext {

    // The current lexical scope's mapping from Alloy variable labels to either
    // Fortress Terms (i.e. for quantified vars) or Alloy expressions as used in the "let x = e | ..." construct.
    // We use a single Env so these types of mappings can shadow each other.
    private Env<String, Either<AnnotatedTerm, LetContext>> alloyVarMapping;

    public VarMappingContext() {
        this.alloyVarMapping = new Env<>();
    }

    public VarMappingContext(VarMappingContext varMappingContext) {
        this.alloyVarMapping = varMappingContext.alloyVarMapping.dup();
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
    }

}