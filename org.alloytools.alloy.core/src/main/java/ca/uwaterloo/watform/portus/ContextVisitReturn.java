package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.List;

/**
 * A specialization of {@link FortressVisitReturn} which holds a context and handles
 * updating it when visiting lets, etc. We also automatically expand variables
 * which have let mappings in the context.
 * Note that ExprCalls do *not* have their arguments mapped by default, since generally
 * we only process the arguments (which are all handled in the pre-map context).
 */
abstract class ContextVisitReturn<T> extends FortressVisitReturn<T> {

    protected final VarMappingContext varMappingContext;
    private final SortPolicy sortPolicy;

    private static final String PLACEHOLDER_BOUND_VAR_PREFIX = "%boundPlaceholderVar%";

    public ContextVisitReturn(VarMappingContext varMappingContext, SortPolicy sortPolicy) {
        // Don't copy because rangeAssigner has side effects which need to be persisted
        this.varMappingContext = varMappingContext;
        this.sortPolicy = sortPolicy;
    }

    public ContextVisitReturn(TranslationContext context, SortPolicy sortPolicy) {
        this(context.varMappingContext, sortPolicy);
    }

    // Quantified variables are mapped to an arbitrary variable satisfying this.
    protected boolean isPlaceholderBoundVar(Var var) {
        return var.name().startsWith(PLACEHOLDER_BOUND_VAR_PREFIX);
    }

    private Var getPlaceholderBoundVar(Sort sort) {
        // use the same one for each sort
        return Term.mkVar(PLACEHOLDER_BOUND_VAR_PREFIX + sort.name());
    }

    @Override
    public final T visit(ExprLet x) throws Err {
        varMappingContext.addLetMapping(x.var.label, x.expr);
        try {
            return visitLet(x);
        } finally {
            varMappingContext.removeMapping(x.var.label);
        }
    }

    public abstract T visitLet(ExprLet x) throws Err;

    /**
     * Visit an ExprQt. Note that any quantified variables after one with sorts resolving to none will not
     * be added to the context!
     */
    @Override
    public final T visit(ExprQt x) throws Err {
        // add var mappings for the quantified variables as we move into the quantifier
        List<T> argResults = new ArrayList<>();
        List<String> varNamesAdded = new ArrayList<>();
        List<Var> placeholderBoundVars = new ArrayList<>();
        try {
            for (Decl decl : x.decls) {
                for (ExprHasName name : decl.names) {
                    argResults.add(visitQuantifierArg(decl.expr));

                    SortResolvant resolvant = sortPolicy.getMinimalExprSorts(decl.expr, varMappingContext);
                    if (resolvant.isNone()) {
                        // If the resolvant is none, **do not visit any further variables or add them to the context**.
                        // This is because we always short-circuit any quantifiers with none sorts, so we do not
                        // recurse into them. This is necessary for Portus to work with e.g. "some x: none | ...".
                        // THIS MAY CAUSE BUGS! THIS IS A LIKELY SPOT FOR ODD BEHAVIOUR!
                        return visitQuantifier(x, argResults, true);
                    }

                    if (!resolvant.isDefinite()) {
                        throw new ErrorNoPortusSupport("Quantifier decl expression must have definite sorts!");
                    }
                    if (resolvant.arity() > 1) {
                        throw new ErrorNoPortusSupport("Portus only supports unary quantifier decl expressions!");
                    }
                    Sort sort = resolvant.getDefiniteSorts().get(0);
                    Var placeholderBoundVar = getPlaceholderBoundVar(sort);
                    varMappingContext.addTermMapping(name.label, new AnnotatedTerm(placeholderBoundVar.of(sort)));
                    varMappingContext.addFortressVar(placeholderBoundVar.of(sort));
                    varNamesAdded.add(name.label);
                    placeholderBoundVars.add(placeholderBoundVar);
                }
            }
            return visitQuantifier(x, argResults, false);
        } finally {
            // remove the var mappings in reverse order
            for (int i = varNamesAdded.size() - 1; i >= 0; i--) {
                varMappingContext.removeMapping(varNamesAdded.get(i));
            }
            for (int i = placeholderBoundVars.size() - 1; i >= 0; i--) {
                varMappingContext.removeFortressVar(placeholderBoundVars.get(i));
            }
        }
    }

    /**
     * Called for quantifiers after visiting the arguments..
     * argResults is the result of visitQuantifierArg called for each quantifier argument.
     * anyArgNone indicates whether any argument's sorts statically evaluated to none, in which case
     * visitQuantifierArg was not called for it and subsequent arguments and those arguments were not
     * added to the context. Implementations should short-circuit if this is set.
     */
    public abstract T visitQuantifier(ExprQt x, List<T> argResults, boolean anyArgNone) throws Err;

    /** Called for each quantified variable expression; results are passed in argResults in visitQuantifier. */
    public T visitQuantifierArg(Expr arg) throws Err {
        return null;
    }

    @Override
    public final T visit(ExprVar x) throws Err {
        // Expand the let mapping if it has it
        if (varMappingContext.hasLetMapping(x.label)) {
            VarMappingContext.LetContext letContext = varMappingContext.getLetMapping(x.label);
            assert letContext != null;
            letContext.useLetMapping(varMappingContext);
            try {
                return visitLetVarExpr(letContext.getExpr());
            } finally {
                letContext.resetMapping();
            }
        } else {
            return visitVar(x);
        }
    }

    public abstract T visitVar(ExprVar x) throws Err;

    /**
     * Visit the expression pointed to by a var with a let mapping.
     * Can be overriden to take advantage of ContextVisitReturn's let-expansion without automatically recursing.
     */
    public T visitLetVarExpr(Expr expr) throws Err {
        return visitThis(expr);
    }

    /** A base implementation of ContextVisitReturn that by default returns null from each method. */
    static class Default<T> extends ContextVisitReturn<T> {
        public Default(TranslationContext context, SortPolicy sortPolicy) {
            super(context, sortPolicy);
        }

        @Override
        public T visitLet(ExprLet x) throws Err {
            return null;
        }

        @Override
        public T visitQuantifier(ExprQt x, List<T> argResults, boolean anyArgNone) throws Err {
            return null;
        }

        @Override
        public T visitVar(ExprVar x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprElementOf x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprBinary x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprList x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprCall x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprConstant x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprITE x) throws Err {
            return null;
        }

        @Override
        public T visit(ExprUnary x) throws Err {
            return null;
        }

        @Override
        public T visit(Sig x) throws Err {
            return null;
        }

        @Override
        public T visit(Sig.Field x) throws Err {
            return null;
        }

        @Override
        public T visit(Func x) throws Err {
            return null;
        }

        @Override
        public T visit(Assert x) throws Err {
            return null;
        }

        @Override
        public T visit(Macro macro) throws Err {
            return null;
        }
    }

}
