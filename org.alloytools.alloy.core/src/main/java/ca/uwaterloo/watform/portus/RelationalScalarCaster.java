package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.List;

/**
 * This scalar caster combines scalars into larger ones using relational operators.
 */
final class RelationalScalarCaster implements ScalarCaster {

    private final Translator translator;
    private final ScalarCaster rootScalarCaster;
    private final SortPolicy sortPolicy;

    public RelationalScalarCaster(Translator translator, ScalarCaster rootScalarCaster, SortPolicy sortPolicy) {
        this.translator = translator;
        this.rootScalarCaster = rootScalarCaster;
        this.sortPolicy = sortPolicy;
    }

    @Override
    public String name() {
        return "Relational Scalar Caster";
    }

    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        if (expr instanceof ExprBinary) {
            ExprBinary binary = (ExprBinary) expr;
            if (binary.op == ExprBinary.Op.INTERSECT) {
                return castIntersection(binary.left, binary.right, context);
            } else if (binary.op == ExprBinary.Op.MINUS) {
                return castSetMinus(binary.left, binary.right, context);
            } else if (binary.op == ExprBinary.Op.DOMAIN) {
                return castDomainRestriction(binary.left, binary.right, context);
            } else if (binary.op == ExprBinary.Op.RANGE) {
                return castRangeRestriction(binary.left, binary.right, context);
            } else if (binary.op.isArrow) {
                return castArrow(binary.left, binary.right, context);
            } else if (binary.op == ExprBinary.Op.PLUSPLUS) {
                return castOverride(binary.left, binary.right, context);
            }
        } else if (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            if (unary.op == ExprUnary.Op.TRANSPOSE) {
                Expr sub = PortusUtil.stripPortusNoops(unary.sub);
                if (sub instanceof ExprBinary) {
                    ExprBinary subBinary = (ExprBinary) sub;
                    if (subBinary.op.isArrow) {
                        return castTransposeArrow(subBinary.left, subBinary.right, context);
                    }
                }
            }
        }
        return null;
    }

    /**
     * If castToScalar(e1) = (e1, guard1), then castToScalar(e1 & e2) = (e1, x -> guard1(x) && [[(x,e1(x)) \in e2]]),
     * and vice versa. This will be further optimized if e2 is also a scalar.
     */
    private Scalar castIntersection(Expr left, Expr right, TranslationContext context) {
        // Figure out which one is the scalar: we'll end up casting "scalar & expr".
        Scalar scalar;
        Expr expr;

        Scalar leftScalar = rootScalarCaster.castToScalar(left, context);
        if (leftScalar != null) {
            scalar = leftScalar;
            expr = right;
        } else {
            Scalar rightScalar = rootScalarCaster.castToScalar(right, context);
            if (rightScalar != null) {
                scalar = rightScalar;
                expr = left;
            } else {
                return null; // neither
            }
        }

        Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                scalar.getGuard(tuple, newContext),
                translator.translate(ExprElementOf.make(
                        tuple.concat(new TermTuple(scalar.getAnnotatedScalar(tuple, newContext))), expr), newContext));
        return new Scalar(
                scalar.getArgSorts(), scalar.getResultSort(), scalar.getScalarGenerator(), guardGenerator, context);
    }

    /**
     * If castToScalar(e1) = (e1, guard1), then castToScalar(e1 - e2) = (e1, x -> guard1(x) && ![[(x,e1(x)) \in e2]]).
     * This will be further optimized if e2 is also a scalar.
     */
    private Scalar castSetMinus(Expr left, Expr right, TranslationContext context) {
        Scalar scalar = rootScalarCaster.castToScalar(left, context);
        if (scalar == null) {
            return null;
        }

        Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                scalar.getGuard(tuple, newContext),
                Term.mkNot(translator.translate(ExprElementOf.make(
                        tuple.concat(new TermTuple(scalar.getAnnotatedScalar(tuple, newContext))), right),
                        newContext)));
        return new Scalar(
                scalar.getArgSorts(), scalar.getResultSort(), scalar.getScalarGenerator(), guardGenerator, context);
    }

    /**
     * If castToScalar(e2) = (e2, guard2), then castToScalar(e1 <: e2) = (e2, x -> guard2(x) && [[x[0] \in e1]]).
     * This will be further optimized if e1 is also a scalar.
     */
    private Scalar castDomainRestriction(Expr left, Expr right, TranslationContext context) {
        Scalar scalar = rootScalarCaster.castToScalar(right, context);
        if (scalar == null) {
            return null;
        }

        Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                scalar.getGuard(tuple, newContext),
                translator.translate(ExprElementOf.make(tuple.getAnnotatedTerm(0), left), newContext));
        return new Scalar(
                scalar.getArgSorts(), scalar.getResultSort(), scalar.getScalarGenerator(), guardGenerator, context);
    }

    /**
     * If castToScalar(e1) = (e1, guard1), then castToScalar(e1 :> e2) = (e1, x -> guard1(x) && [[e1(x) \in e2]]).
     * Also, if castToScalar(e2) = (e2, guard2) nilary, then
     *     castToScalar(e1 :> e2) = (e2, x -> guard2 && [[(x, e2) \in e1]]).
     * If both are scalars, these are equivalent.
     */
    private Scalar castRangeRestriction(Expr left, Expr right, TranslationContext context) {
        Scalar leftScalar = rootScalarCaster.castToScalar(left, context);
        if (leftScalar != null) {
            // First optimization
            Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                    leftScalar.getGuard(tuple, newContext),
                    translator.translate(
                            ExprElementOf.make(leftScalar.getAnnotatedScalar(tuple, newContext), right), newContext));
            return new Scalar(leftScalar.getArgSorts(), leftScalar.getResultSort(), leftScalar.getScalarGenerator(),
                    guardGenerator, context);
        }

        Scalar rightScalar = rootScalarCaster.castToScalar(right, context);
        if (rightScalar != null) {
            if (!rightScalar.isNilary()) {
                throw new ErrorFatal("Right-hand side of a :> expression must have arity 1!");
            }

            // Second optimization
            Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                    rightScalar.getNilaryGuard(newContext),
                    translator.translate(ExprElementOf.make(
                            tuple.concat(new TermTuple(rightScalar.getNilaryAnnotatedScalar(newContext))), left),
                            newContext));
            return new Scalar(rightScalar.getArgSorts(), rightScalar.getResultSort(), rightScalar.getScalarGenerator(),
                    guardGenerator, context);
        }

        return null;
    }

    /**
     * If castToScalar(e2) = (e2, guard2) and e1 has definite sorts then
     *   castToScalar(e1->e2) = ((x,y) -> e2(y), (x,y) -> guard2(y) && [[x \in e1]]).
     * This is optimized further if e1 is a scalar.
     */
    private Scalar castArrow(Expr left, Expr right, TranslationContext context) {
        Scalar rightScalar = rootScalarCaster.castToScalar(right, context);
        if (rightScalar == null) {
            return null;
        }

        SortResolvant leftSorts = sortPolicy.getMinimalExprSorts(left, context);
        if (!leftSorts.isDefinite()) {
            return null;
        }
        List<Sort> argSorts = SetOps.concatenate(leftSorts.getDefiniteSorts(), rightScalar.getArgSorts());

        int leftArity = left.type().arity();
        int rightArity = rightScalar.getArity();
        Scalar.TermGenerator scalarGenerator = (tuple, newContext) ->
                rightScalar.getScalar(tuple.slice(leftArity, leftArity + rightArity), context);
        Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                rightScalar.getGuard(tuple.slice(leftArity, leftArity + rightArity), newContext),
                translator.translate(ExprElementOf.make(tuple.slice(0, leftArity), left), newContext));
        return new Scalar(argSorts, rightScalar.getResultSort(), scalarGenerator, guardGenerator, context);
    }

    /**
     * If castToScalar(e1) = (e1, guard1) and e2 has arity 1 and definite sorts then
     *   castToScalar(~(e1->e2)) = (x -> e1, x -> guard1 && [[x \in e2]]).
     * This is optimized further if e2 is a scalar.
     */
    private Scalar castTransposeArrow(Expr left, Expr right, TranslationContext context) {
        if (left.type().arity() != 1 || right.type().arity() != 1) {
            // shouldn't have typechecked, but check anyways
            return null;
        }

        Scalar leftScalar = rootScalarCaster.castToScalar(left, context);
        if (leftScalar == null || !leftScalar.isNilary()) {
            return null;
        }

        SortResolvant rightSorts = sortPolicy.getMinimalExprSorts(right, context);
        if (!rightSorts.isDefinite() || rightSorts.arity() != 1) {
            return null;
        }
        List<Sort> argSorts = rightSorts.getDefiniteSorts();

        Scalar.TermGenerator scalarGenerator = (tuple, newContext) -> leftScalar.getNilaryScalar(newContext);
        Scalar.TermGenerator guardGenerator = (tuple, newContext) -> Term.mkAnd(
                    leftScalar.getNilaryGuard(newContext),
                    translator.translate(ExprElementOf.make(tuple, right), newContext));
        return new Scalar(argSorts, leftScalar.getResultSort(), scalarGenerator, guardGenerator, context);
    }

    /**
     * If castToScalar(e1) = (e1, guard1) and castToScalar(e2) = (e2, guard2) with compatible sorts then
     *   castToScalar(e1 ++ e2) = (e1 ++ e2, guard1 ++ guard2)
     * where ++ is as described in {@link Scalar#override}.
     */
    private Scalar castOverride(Expr left, Expr right, TranslationContext context) {
        Scalar leftScalar = rootScalarCaster.castToScalar(left, context);
        if (leftScalar == null) {
            return null;
        }
        Scalar rightScalar = rootScalarCaster.castToScalar(right, context);
        if (rightScalar == null) {
            return null;
        }
        if (!leftScalar.hasSameSignature(rightScalar)) {
            // probably will get short-circuited anyways
            return null;
        }
        if (leftScalar.getArity() != 2) {
            // doesn't apply to arity > 2, wrong semantics for Alloy ++
            return null;
        }
        return Scalar.override(leftScalar, rightScalar, context.getVarMappingContext());
    }

}
