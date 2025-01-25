package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Assert;
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
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

/**
 * A scalar caster which casts simple expressions to scalars which don't need any additional state.
 * Note: We currently don't translate boolean-valued expressions to scalars, because it's probably not necessary.
 */
final class DefaultScalarCaster implements ScalarCaster {

    // The list of builtin constants that we can treat like scalars.
    // String is handled by StringTranslator.
    private static final ConstList<ExprConstant.Op> SCALAR_CONSTANTS = ConstList.make(Arrays.asList(
            ExprConstant.Op.TRUE,
            ExprConstant.Op.FALSE,
            ExprConstant.Op.NUMBER,
            ExprConstant.Op.MIN,
            ExprConstant.Op.MAX));

    // The list of unary operations that will return scalars.
    private static final ConstList<ExprUnary.Op> INT_UNARY_OPS = ConstList.make(Collections.singletonList(
            ExprUnary.Op.CARDINALITY));

    // The list of binary operations that will return scalars.
    private static final ConstList<ExprBinary.Op> INT_BINARY_OPS = ConstList.make(Arrays.asList(
            ExprBinary.Op.IPLUS,
            ExprBinary.Op.IMINUS,
            ExprBinary.Op.MUL,
            ExprBinary.Op.DIV,
            ExprBinary.Op.REM));

    // The translator to use when we need to translate something while casting to scalar.
    private final Translator translator;

    // The scalar caster to use for recursive casting.
    private final ScalarCaster rootScalarCaster;

    private final SortPolicy sortPolicy;

    public DefaultScalarCaster(Translator translator, ScalarCaster rootScalarCaster, SortPolicy sortPolicy) {
        this.translator = translator;
        this.rootScalarCaster = rootScalarCaster;
        this.sortPolicy = sortPolicy;
    }

    @Override
    public String name() {
        return "Default";
    }

    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        return new ContextVisitReturn<Scalar>(context, sortPolicy) {
            private Scalar castByTranslating(Expr expr, Sort sort) {
                // Translate as an expression of type `sort` and just use that
                Term scalar = translator.translate(expr, context);
                assert scalar != null;

                // Assume no guard on usage needed.
                return new Scalar(new AnnotatedTerm(scalar, sort), Term.mkTop());
            }

            @Override
            public Scalar visit(ExprList x) throws Err {
                // None of the operators return scalars
                return null;
            }

            @Override
            public Scalar visit(ExprCall call) {
                // Cast the body
                varMappingContext.addLetMappingsFromCall(call);
                try {
                    return rootScalarCaster.castToScalar(call.fun.getBody(), context);
                } finally {
                    varMappingContext.removeLetMappingsFromCall(call);
                }
            }

            @Override
            public Scalar visit(ExprConstant x) {
                if (SCALAR_CONSTANTS.contains(x.op)) {
                    // Translate it as an integer/boolean expression and just use that
                    // Determine the Fortress sort: true, false are boolean, rest are integers
                    Sort sort = (x.op == ExprConstant.Op.TRUE || x.op == ExprConstant.Op.FALSE)
                            ? Sort.Bool()
                            : Sort.Int();
                    return castByTranslating(x, sort);
                }
                return null;
            }

            @Override
            public Scalar visit(ExprUnary x) {
                // Strip noops. Note if the noop is cast2int and casting fails, IntSumScalarCaster will run if enabled.
                Expr denooped = PortusUtil.stripPortusNoops(x);
                if (denooped != x) {
                    return rootScalarCaster.castToScalar(denooped, context);
                }

                if (INT_UNARY_OPS.contains(x.op)) {
                    // Translate as an integer expression (they all return int)
                    return castByTranslating(x, Sort.Int());
                }
                return null;
            }

            @Override
            public Scalar visit(ExprBinary x) {
                if (INT_BINARY_OPS.contains(x.op)) {
                    // Translate as an integer expression (they all return int)
                    return castByTranslating(x, Sort.Int());
                }
                return null;
            }

            @Override
            public Scalar visit(ExprITE x) {
                // If both branches are scalars, we can translate the whole ITE as a scalar
                Scalar leftScalar = rootScalarCaster.castToScalar(x.left, context);
                if (leftScalar == null) {
                    return null;
                }
                Scalar rightScalar = rootScalarCaster.castToScalar(x.right, context);
                if (rightScalar == null) {
                    return null;
                }

                // If the arities/arg sorts/result sorts aren't compatible, let someone else deal with it
                if (!leftScalar.hasSameSignature(rightScalar)) {
                    return null;
                }
                List<Sort> argSorts = leftScalar.getArgSorts();
                Sort resultSort = leftScalar.getResultSort();

                // scalar is "condition => left else right", guard is "condition => guardLeft else guardRight"
                // (we have to repeat condition in normal translation anyways, so it should be fine)
                Term condition = translator.translate(x.cond, context);
                Function<TermTuple, Term> scalarGenerator = tuple ->
                        Term.mkIfThenElse(condition, leftScalar.getScalar(tuple), rightScalar.getScalar(tuple));
                Function<TermTuple, Term> guardGenerator = tuple ->
                        Term.mkIfThenElse(condition, leftScalar.getGuard(tuple), rightScalar.getGuard(tuple));
                return new Scalar(argSorts, resultSort, scalarGenerator, guardGenerator);
            }

            @Override
            public Scalar visit(Sig sig) {
                // one sigs are handled in OneSigOptTranslator
                return null;
            }

            @Override
            public Scalar visit(Sig.Field x) {
                // No field can be a scalar on its own because no field is unary (always the sig on the left)
                return null;
            }

            @Override
            public Scalar visit(ExprElementOf x) {
                // ExprElementOf is always boolean, which we don't bother casting to scalar
                return null;
            }

            @Override
            public Scalar visitLet(ExprLet x) {
                // The mappings are already taken care of for us, so just cast the body
                return rootScalarCaster.castToScalar(x.sub, context);
            }

            @Override
            public Scalar visitQuantifier(
                    ExprQt x, List<Scalar> argResults, boolean anyArgNone) {
                // Sum can be cast to scalar by translating since it's an int
                if (x.op == ExprQt.Op.SUM) {
                    return castByTranslating(x, Sort.Int());
                }
                return null;
            }

            @Override
            public Scalar visitVar(ExprVar x) {
                // Check for mappings to scalars - lets handled for us
                if (varMappingContext.hasTermMapping(x.label)) {
                    AnnotatedTerm fortressTerm = varMappingContext.getTermMapping(x.label);
                    assert fortressTerm != null;
                    // no guard on the variable usage is needed
                    return new Scalar(fortressTerm, Term.mkTop());
                }
                return null;
            }

            @Override
            public Scalar visitLetVarExpr(Expr expr) throws Err {
                // When super unwraps a let var for us, let all casters have a chance to cast it.
                return rootScalarCaster.castToScalar(expr, context);
            }

            @Override
            public Scalar visit(Func x) throws Err {
                return null; // This probably shouldn't appear
            }

            @Override
            public Scalar visit(Assert x) throws Err {
                return null; // This also probably shouldn't appear
            }

            @Override
            public Scalar visit(Macro macro) throws Err {
                return null; // This also probably shouldn't appear
            }
        }.visitThis(expr);
    }

}
