package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.VisitReturn;
import fortress.msfol.Term;

import java.util.UUID;

/**
 * A convenience base implementation of Translator. Immutable.
 * Provides conveniences like managing reporters, an intuitive API for
 * recursively translating expressions, and subclass-specific translate() overloads.
 * Most translators should extend this class.
 */
abstract class BaseTranslator implements Translator {

    // The Translator used for recursive translation.
    // We can't just call translate() because that wouldn't give other translators
    // the chance to translate.
    private final Translator topLevelTranslator;

    private final Visitor visitor = new Visitor();

    /**
     * Create a translator with some convenience fields.
     * @param topLevel The top-level translator that recursive translate() calls
     *                 from this translator will delegate to.
     */
    public BaseTranslator(Translator topLevel) {
        this.topLevelTranslator = topLevel;
    }

    /**
     * Translate an expression. This method *must* be used when recursively
     * translating from within a translator in order to let the top-level
     * translator manage the translation.
     *
     * @param expr The Alloy expression to recursively translate.
     * @param context The context for the translation as updated so far.
     * @return The Fortress translation for the expression.
     */
    protected Term recursivelyTranslate(
            Expr expr, TranslationContext context) {
        return topLevelTranslator.translate(expr, context);
    }

    // The following are convenience methods for translating particular Expr subclasses.
    // Calls to translate() will automatically be routed to one of these methods.

    /** Translate an ExprBinary Alloy node. */
    public Term translate(ExprBinary expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprList Alloy node. */
    public Term translate(ExprList expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprCall Alloy node. */
    public Term translate(ExprCall expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprConstant Alloy node. */
    public Term translate(ExprConstant expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprITE Alloy node. */
    public Term translate(ExprITE expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprLet Alloy node. */
    public Term translate(ExprLet expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprQt Alloy node. */
    public Term translate(ExprQt expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprUnary Alloy node. */
    public Term translate(ExprUnary expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprVar Alloy node. */
    public Term translate(ExprVar expr, TranslationContext context) {
        return null;
    }

    /**
     * Translate an Alloy signature.
     * For sigs and other Exprs that do not have values, the return value should be Top if
     * successful, and the context should be updated.
     */
    public Term translate(Sig expr, TranslationContext context) {
        return null;
    }

    /** Translate an Alloy field. */
    public Term translate(Sig.Field expr, TranslationContext context) {
        return null;
    }

    /**
     * Translate an Alloy expression to a Fortress context.
     *
     * Do not call this recursively from subclasses! Instead, use
     * {@link #recursivelyTranslate(Expr, TranslationContext)} to give other translators
     * a chance to run.
     */
    @Override
    public final Term translate(Expr expr, TranslationContext context) {
        return visitor.delegate(expr, context);
    }

    // Helper for delegating based on type of expression.
    // TODO: any advantage over just a switch statement? perf cost?
    private final class Visitor extends VisitReturn<Term> {

        private TranslationContext context = null;

        Term delegate(Expr expr, TranslationContext context) {
            this.context = context;
            Term result = visitThis(expr);
            this.context = null;
            return result;
        }

        @Override
        public Term visit(ExprBinary expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprList expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprCall expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprConstant expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprITE expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprLet expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprQt expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprUnary expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprVar expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(Sig expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(Sig.Field expr) throws Err {
            return translate(expr, context);
        }

    }

    /** Create a unique name for a Fortress symbol. */
    public String makeUniqueName(String name) {
        return name + "$" + UUID.randomUUID();
    }

}
