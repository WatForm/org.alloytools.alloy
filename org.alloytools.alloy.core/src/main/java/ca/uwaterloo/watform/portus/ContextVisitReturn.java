package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

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

    protected final TranslationContext context;

    // The placeholder which bound variables will be mapped to in the context.
    protected final AnnotatedVar boundPlaceholderVar = Term.mkVar("%boundPlaceholderVar").of(Sort.Int());

    public ContextVisitReturn(TranslationContext context) {
        // Make a copy just in case
        this.context = new TranslationContext(context);
    }

    @Override
    public final T visit(ExprLet x) throws Err {
        context.addLetMapping(x.var.label, x.expr);
        try {
            return visitLet(x);
        } finally {
            context.removeMapping(x.var.label);
        }
    }

    public abstract T visitLet(ExprLet x) throws Err;

    @Override
    public final T visit(ExprQt x) throws Err {
        // add var mappings for the quantified variables as we move into the quantifier
        List<T> argResults = new ArrayList<>();
        for (Decl decl : x.decls) {
            for (ExprHasName name : decl.names) {
                argResults.add(visitQuantifierArg(decl.expr));
                context.addTermMapping(name.label, new AnnotatedTerm(boundPlaceholderVar));
            }
        }
        try {
            return visitQuantifier(x, argResults);
        } finally {
            // remove the var mappings
            for (Decl decl : x.decls) {
                for (ExprHasName name : decl.names) {
                    context.removeMapping(name.label);
                }
            }
        }
    }

    public abstract T visitQuantifier(ExprQt x, List<T> argResults) throws Err;

    /** Called for each quantified variable expression; results are passed in argResults in visitQuantifier. */
    public T visitQuantifierArg(Expr arg) throws Err {
        return null;
    }

    @Override
    public final T visit(ExprVar x) throws Err {
        // Expand the let mapping if it has it
        if (context.hasLetMapping(x.label)) {
            TranslationContext.LetContext letContext = context.getLetMapping(x.label);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return visitThis(letContext.getExpr());
            } finally {
                letContext.resetMapping();
            }
        } else {
            return visitVar(x);
        }
    }

    public abstract T visitVar(ExprVar x) throws Err;

}
