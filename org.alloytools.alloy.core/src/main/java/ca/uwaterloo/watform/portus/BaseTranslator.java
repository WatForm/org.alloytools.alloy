package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
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
import fortress.msfol.Theory;

/**
 * A convenience base implementation of Translator. Immutable.
 * Provides conveniences like managing reporters, an intuitive API for
 * recursively translating expressions, and subclass-specific translate() overloads.
 * Most translators should extend this class.
 */
abstract class BaseTranslator implements Translator {

    // A reporter that subclasses can use to log output.
    protected final A4Reporter reporter;

    // The Translator used for recursive translation.
    // We can't just call translate() because that wouldn't give other translators
    // the chance to translate.
    private final Translator topLevelTranslator;
    
    private final Visitor visitor = new Visitor();

    /**
     * Create a translator with some convenience fields.
     * @param reporter A reporter subclasses can use to log output (can be null).
     * @param topLevel The top-level translator that recursive translate() calls
     *                 from this translator will delegate to.
     */
    public BaseTranslator(A4Reporter reporter, Translator topLevel) {
        this.reporter = (reporter == null) ? A4Reporter.NOP : reporter;
        this.topLevelTranslator = topLevel;
    }

    /**
     * Translate an expression. This method *must* be used when recursively
     * translating from within a translator in order to let the top-level
     * translator manage the translation.
     */
    protected Theory recursivelyTranslate(Expr expr, Theory base) {
        return topLevelTranslator.translate(expr, base);
    }

    // The following are convenience methods for translating particular Expr subclasses.
    // Calls to translate() will automatically be routed to one of these methods.

    /** Translate an ExprBinary Alloy node. */
    public Theory translate(ExprBinary expr, Theory base) {
        return null;
    }

    /** Translate an ExprList Alloy node. */
    public Theory translate(ExprList expr, Theory base) {
        return null;
    }

    /** Translate an ExprCall Alloy node. */
    public Theory translate(ExprCall expr, Theory base) {
        return null;
    }

    /** Translate an ExprConstant Alloy node. */
    public Theory translate(ExprConstant expr, Theory base) {
        return null;
    }

    /** Translate an ExprITE Alloy node. */
    public Theory translate(ExprITE expr, Theory base) {
        return null;
    }

    /** Translate an ExprLet Alloy node. */
    public Theory translate(ExprLet expr, Theory base) {
        return null;
    }

    /** Translate an ExprQt Alloy node. */
    public Theory translate(ExprQt expr, Theory base) {
        return null;
    }

    /** Translate an ExprUnary Alloy node. */
    public Theory translate(ExprUnary expr, Theory base) {
        return null;
    }

    /** Translate an ExprVar Alloy node. */
    public Theory translate(ExprVar expr, Theory base) {
        return null;
    }

    /** Translate an Alloy signature. */
    public Theory translate(Sig expr, Theory base) {
        return null;
    }

    /** Translate an Alloy field. */
    public Theory translate(Sig.Field expr, Theory base) {
        return null;
    }

    /**
     * Translate an Alloy expression to a Fortress theory.
     *
     * Do not call this recursively from subclasses! Instead, use
     * {@link #recursivelyTranslate(Expr, Theory)} to give other translators
     * a chance to run.
     */
    @Override
    public final Theory translate(Expr expr, Theory base) {
        // TODO delegate to above
        return visitor.delegate(expr, base);
    }

    // Helper for delegating based on type of expression.
    // TODO: any advantage over just a switch statement? perf cost?
    private final class Visitor extends VisitReturn<Theory> {

        private Theory theory = null;

        Theory delegate(Expr expr, Theory theory) {
            this.theory = theory;
            Theory result = visitThis(expr);
            this.theory = null;
            return result;
        }

        @Override
        public Theory visit(ExprBinary expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprList expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprCall expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprConstant expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprITE expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprLet expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprQt expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprUnary expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(ExprVar expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(Sig expr) throws Err {
            return translate(expr, theory);
        }

        @Override
        public Theory visit(Sig.Field expr) throws Err {
            return translate(expr, theory);
        }

    }

}
