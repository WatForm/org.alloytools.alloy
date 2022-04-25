package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.UniqueNameGenerator;
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
import fortress.msfol.Term;
import fortress.msfol.Var;

/**
 * A convenience base implementation of Translator. Immutable.
 * Provides conveniences like managing reporters, an intuitive API for
 * recursively translating expressions, and subclass-specific translate() overloads.
 * Most translators should extend this class.
 */
abstract class AbstractTranslator implements Translator {

    // The Translator used for recursive translation.
    // We can't just call translate() because that wouldn't give other translators
    // the chance to translate.
    private final Translator topLevelTranslator;

    // Convenience object to make unique names.
    protected final UniqueNameGenerator uniqueNameGenerator = new UniqueNameGenerator();

    private final Visitor visitor = new Visitor();

    /**
     * Create a translator with some convenience fields.
     * @param topLevel The top-level translator that recursive translate() calls
     *                 from this translator will delegate to.
     */
    public AbstractTranslator(Translator topLevel) {
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

    /** Translate "tuple \in expr", where expr is an ExprBinary term. */
    public Term translate(ConstList<Var> tuple, ExprBinary expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprBinary Alloy formula. */
    public Term translate(ExprBinary expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprList Alloy formula. */
    public Term translate(ExprList expr, TranslationContext context) {
        return null;
    }

    /** Translate a predicate ExprCall Alloy formula. `expr` must be a predicate. */
    public Term translate(ExprCall expr, TranslationContext context) {
        return null;
    }

    /**
     * Translate "tuple \in expr", where expr is a function ExprCall. `expr` must be a function.
     * The arity of `tuple` must match that of `expr`.
     */
    public Term translate(ConstList<Var> tuple, ExprCall expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprConstant Alloy formula. */
    public Term translate(ExprConstant expr, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in expr", where expr is an ExprConstant. */
    public Term translate(ConstList<Var> tuple, ExprConstant expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprITE Alloy formula. */
    public Term translate(ExprITE expr, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in expr", where expr is an ExprITE. */
    public Term translate(ConstList<Var> tuple, ExprITE expr, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in expr", where expr is an ExprLet. Arities must match. */
    public Term translate(ConstList<Var> tuple, ExprLet expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprLet Alloy formula. */
    public Term translate(ExprLet expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprQt Alloy formula. */
    public Term translate(ExprQt expr, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in expr", where expr is an ExprUnary. Arities must match. */
    public Term translate(ConstList<Var> tuple, ExprUnary expr, TranslationContext context) {
        return null;
    }

    /** Translate an ExprUnary Alloy formula. */
    public Term translate(ExprUnary expr, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in expr", where expr is an ExprVar. */
    public Term translate(ConstList<Var> tuple, ExprVar expr, TranslationContext context) {
        return null;
    }

    /**
     * Translate an Alloy primitive signature declaration.
     * For sig declarations and other Exprs that do not have values, the return value should be
     * Top if successful, and the context should be updated.
     */
    public Term translate(Sig.PrimSig sig, TranslationContext context) {
        return null;
    }

    /**
     * Translate an Alloy subset signature declaration.
     * Again, return Top and update the context if successful.
     */
    public Term translate(Sig.SubsetSig sig, TranslationContext context) {
        return null;
    }

    /** Translate "var \in sig" for an Alloy signature `sig`. */
    public Term translate(Var var, Sig sig, TranslationContext context) {
        return null;
    }

    /** Translate an Alloy field declaration. */
    public Term translate(Sig.Field field, TranslationContext context) {
        return null;
    }

    /** Translate "tuple \in field" for an Alloy field `field`. Arities must match. */
    public Term translate(ConstList<Var> tuple, Sig.Field field, TranslationContext context) {
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
    private final class Visitor extends FortressVisitReturn<Term> {

        private TranslationContext context = null;

        Term delegate(Expr expr, TranslationContext context) {
            this.context = context;
            Term result = visitThis(expr);
            this.context = null;
            return result;
        }

        // When visiting ExprElementOf, pass down contextual info.
        @Override
        public Term visit(ExprElementOf expr) throws Err {
            if (expr.sub instanceof ExprBinary) {
                return translate(expr.tuple, (ExprBinary) expr.sub, context);
            } else if (expr.sub instanceof ExprUnary) {
                return translate(expr.tuple, (ExprUnary) expr.sub, context);
            } else if (expr.sub instanceof ExprVar) {
                return translate(expr.tuple, (ExprVar) expr.sub, context);
            } else if (expr.sub instanceof ExprCall) {
                ExprCall call = (ExprCall) expr.sub;
                if (call.fun.isPred) {
                    throw new ErrorFatal("Predicate ExprCalls must not be wrapped with ExprElementOf.");
                }
                // it's a function: pass down the contextual info
                return translate(expr.tuple, call, context);
            } else if (expr.sub instanceof ExprConstant) {
                return translate(expr.tuple, (ExprConstant) expr.sub, context);
            } else if (expr.sub instanceof ExprLet) {
                return translate(expr.tuple, (ExprLet) expr.sub, context);
            } else if (expr.sub instanceof ExprITE) {
                return translate(expr.tuple, (ExprITE) expr.sub, context);
            } else if (expr.sub instanceof Sig) {
                assert expr.tuple.size() == 1;
                return translate(expr.tuple.get(0), (Sig) expr.sub, context);
            } else if (expr.sub instanceof Sig.Field) {
                return translate(expr.tuple, (Sig.Field) expr.sub, context);
            } else {
                StringBuilder builder = new StringBuilder();
                expr.sub.toString(builder, -1);
                throw new ErrorFatal("Bad expression wrapped with ExprElementOf: " + builder);
            }
        }

        @Override
        public Term visit(ExprBinary expr) throws Err {
            // assume it's a formula
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprList expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprCall expr) throws Err {
            if (expr.fun.isPred) {
                return translate(expr, context);
            } else {
                throw new ErrorFatal("Function ExprCalls must be wrapped with ExprElementOf.");
            }
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
            // assume it's a formula
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprQt expr) throws Err {
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprUnary expr) throws Err {
            // assume it's a formula
            return translate(expr, context);
        }

        @Override
        public Term visit(ExprVar expr) throws Err {
            // not a formula: must wrap it to pass down contextual info
            throw new ErrorFatal("ExprVar must be wrapped with ExprElementOf");
        }

        @Override
        public Term visit(Sig.PrimSig expr) throws Err {
            // assume it's a declaration
            return translate(expr, context);
        }

        @Override
        public Term visit(Sig.SubsetSig expr) throws Err {
            // assume it's a declaration
            return translate(expr, context);
        }

        @Override
        public Term visit(Sig.Field expr) throws Err {
            // assume it's a declaration
            return translate(expr, context);
        }

    }

}
