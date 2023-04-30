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
        // Don't copy because rangeAssigner has side effects which need to be persisted
        this.context = context;
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
    public static class Default<T> extends ContextVisitReturn<T> {
        public Default(TranslationContext context) {
            super(context);
        }

        @Override
        public T visitLet(ExprLet x) throws Err {
            return null;
        }

        @Override
        public T visitQuantifier(ExprQt x, List<T> argResults) throws Err {
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
