package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.*;
import fortress.data.NameGenerator;
import fortress.msfol.Term;

import java.util.List;
import java.util.stream.Collectors;

// TODO we might add enough sort policy calls that we have to start caching there
// TODO: THIS REALLY DOES NEED TO BE A PRUNING PREPROCESSOR!
@Deprecated
final class PushdownOptTranslator extends AbstractTranslator implements ScalarCaster {

    private final ScalarCaster rootScalarCaster;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public PushdownOptTranslator(Translator topLevel, ScalarCaster rootScalarCaster, SortPolicy sortPolicy,
                                 NameGenerator nameGenerator) {
        super(topLevel);
        this.rootScalarCaster = rootScalarCaster;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public String name() {
        return "Pushdown";
    }

    /*
    WHAT WE NEED IS RELEVANCE TYPING!!!
    In x \in e, the relevance type information is carried by the sorts of x. (Unfortunately definite.)
    For a full refactor to support this:
    - pass a relevance type whenever castToScalar is called
    - use this in each castToScalar implementation, plus +, to eliminate types

    But for now - shitty simulation with & I guess

    ALSO PUSH DOWN & ???
    castToScalar((a.b)&(A->B)) := castToScalar((a&(A->univ)).(b&(univ->B)))
    - idea is that then it's used to eliminate terms in +
     */

    public static class Pushdown {
        /** Did pushing down change anything? */
        public final boolean effective;

        /** The result of pushing down. */
        public final Expr result;

        public Pushdown(boolean effective, Expr result) {
            this.effective = effective;
            this.result = result;
        }

        public static Pushdown effective(Expr result) {
            return new Pushdown(true, result);
        }

        public static Pushdown ineffective(Expr result) {
            return new Pushdown(false, result);
        }
    }

    public static Expr pushdown(Expr expr) {
        return pushdownWithResult(expr).result;
    }

    // TODO if terms grow too big consider pruning with sort policy here
    public static Pushdown pushdownWithResult(Expr expr) {
        if (expr instanceof ExprBinary) {
            ExprBinary binary = (ExprBinary) expr;
            Pushdown leftResult = pushdownWithResult(PortusUtil.stripPortusNoops(binary.left));
            Pushdown rightResult = pushdownWithResult(PortusUtil.stripPortusNoops(binary.right));
            Expr left = leftResult.result;
            Expr right = rightResult.result;

            if (left instanceof ExprBinary && ((ExprBinary) left).op == ExprBinary.Op.PLUS) {
                ExprBinary leftUnion = (ExprBinary) left;
                if (binary.op == ExprBinary.Op.INTERSECT) {
                    // (a+b)&c -> a&c + b&c
                    return Pushdown.effective(leftUnion.left.intersect(right).plus(leftUnion.right.intersect(right)));
                } else if (binary.op == ExprBinary.Op.JOIN) {
                    // (a+b).c -> a.c + b.c
                    return Pushdown.effective(leftUnion.left.join(right).plus(leftUnion.right.join(right)));
                } else if (binary.op == ExprBinary.Op.RANGE) {
                    // (a+b):>c -> a:>c + b:>c
                    return Pushdown.effective(leftUnion.left.range(right).plus(leftUnion.right.range(right)));
                } else if (binary.op == ExprBinary.Op.MINUS) {
                    // (a+b)-c -> (a-c) + (b-c)
                    // Note pushing down on the right isn't worth it b/c we only get a scalar when left is scalar!
                    return Pushdown.effective(leftUnion.left.minus(right).plus(leftUnion.right.minus(right)));
                }
            }
            if (right instanceof ExprBinary && ((ExprBinary) right).op == ExprBinary.Op.PLUS) {
                ExprBinary rightUnion = (ExprBinary) right;
                if (binary.op == ExprBinary.Op.INTERSECT) {
                    // a&(b+c) -> a&b + a&c
                    return Pushdown.effective(left.intersect(rightUnion.left).plus(left.intersect(rightUnion.right)));
                } else if (binary.op == ExprBinary.Op.JOIN) {
                    // a.(b+c) -> a.b + a.c
                    return Pushdown.effective(left.join(rightUnion.left).plus(left.join(rightUnion.right)));
                } else if (binary.op == ExprBinary.Op.DOMAIN) {
                    // a<:(b+c) -> a<:b + a<:c
                    return Pushdown.effective(left.domain(rightUnion.left).plus(left.domain(rightUnion.right)));
                } else if (binary.op == ExprBinary.Op.ARROW) {
                    // a->(b+c) -> a->b + a->c
                    // Note pushing down on the left isn't worth it b/c we only get a scalar when right is scalar!
                    ExprBinary.Op op = binary.op;
                    return Pushdown.effective(op.make(null, null, left, rightUnion.left)
                            .plus(op.make(null, null, left, rightUnion.right)));
                }
            }
            return new Pushdown(leftResult.effective || rightResult.effective, binary.op.make(null, null, left, right));
        } else if (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            Pushdown subResult = pushdownWithResult(PortusUtil.stripPortusNoops(unary.sub));
            Expr sub = subResult.result;

            if (sub instanceof ExprBinary && ((ExprBinary) sub).op == ExprBinary.Op.PLUS) {
                ExprBinary subUnion = (ExprBinary) sub;
                if (unary.op == ExprUnary.Op.CARDINALITY) {
                    // #(a+b) -> plus[#a, #b]
                    return Pushdown.effective(subUnion.left.cardinality().iplus(subUnion.right.cardinality()));
                } else if (unary.op == ExprUnary.Op.SOME) {
                    // some (a+b) -> (some a) or (some b)
                    return Pushdown.effective(subUnion.left.some().or(subUnion.right.some()));
                } else if (unary.op == ExprUnary.Op.NO) {
                    // no (a+b) -> (no a) and (no b)
                    return Pushdown.effective(subUnion.left.no().and(subUnion.right.no()));
                }
            }
            return new Pushdown(subResult.effective, unary.op.make(null, sub));
        }
        return Pushdown.ineffective(expr);
    }

    private Expr splitToUnion(Expr expr, SortResolvant resolvant) {
        return PreprocessUtil.splitResolvant(resolvant, sortPolicy).stream()
                .map(expr::intersect)
                .reduce(Expr::plus)
                .orElse(ExprConstant.EMPTYNESS);
    }

    /**
     * Handle castToScalar(a + b) when one of a,b short-circuits, and push down other relational operators over
     * union to take advantage of this.
     * TODO move to relational scalar caster
     */
    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
//        Expr pushdownExpr = pushdown(expr);
        if (expr instanceof ExprBinary) {
            ExprBinary binary = (ExprBinary) expr;
            if (binary.op == ExprBinary.Op.PLUS || binary.op == ExprBinary.Op.PLUSPLUS) {
                return castUnionAndOverride(binary.left, binary.right, context);
            }
        }
        return null;
    }

    // castToScalar(a + b) := castToScalar(a) when resolvant(b) = none and vice versa
    // castToScalar(a ++ b) := castToScalar(a) when resolvant(b) = none and castToScalar(b) when resolvant(a) = none
    private Scalar castUnionAndOverride(Expr left, Expr right, TranslationContext context) {
        SortResolvant leftResolvant = sortPolicy.getMinimalExprSorts(left, context);
        if (leftResolvant.isNone()) {
            return rootScalarCaster.castToScalar(right, context);
        }
        SortResolvant rightResolvant = sortPolicy.getMinimalExprSorts(right, context);
        if (rightResolvant.isNone()) {
            return rootScalarCaster.castToScalar(left, context);
        }
        return null;
    }

    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        switch (expr.op) {
            case IN:
                return translateIn(expr.left, expr.right, context);
            case EQUALS:
                return translateEq(expr.left, expr.right, context);
            default:
                return null;
        }
    }

    // [[e1 in e2]] := [[e1&A in e2&A]] && [[e1&B in e2&B]] when resolvant(e1) = {A, B}
    private Term translateIn(Expr left, Expr right, TranslationContext context) {
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(left, context);
        if (resolvant.isNone() || resolvant.isDefinite()) {
            return null; // deal with elsewhere
        }

        List<Term> conjuncts = PreprocessUtil.splitResolvant(resolvant, sortPolicy).stream()
                .map(coveringExpr -> pushdown(left.intersect(coveringExpr).in(right.intersect(coveringExpr))))
                .map(expr -> recursivelyTranslate(expr, context))
                .collect(Collectors.toList());
        return Term.mkAnd(conjuncts);
    }

    // [[e1 = e2]] := [[no e1&A]] && [[e1&B = e2&B]] && [[no e2&C]] when resolvant(e1) = {A, B}, resolvant(e2) = {B, C}
    private Term translateEq(Expr left, Expr right, TranslationContext context) {
        SortResolvant leftResolvant = sortPolicy.getMinimalExprSorts(left, context);
        if (leftResolvant.isNone()) return null;
        SortResolvant rightResolvant = sortPolicy.getMinimalExprSorts(right, context);
        if (rightResolvant.isNone()) return null;
        if (leftResolvant.isDefinite() && rightResolvant.isDefinite()) return null; // handled by default translator

        SortResolvant leftOnly = leftResolvant.difference(rightResolvant);
        SortResolvant rightOnly = rightResolvant.difference(leftResolvant);
        SortResolvant intersection = leftResolvant.intersection(rightResolvant);

        Term noLeftOnlyTerm = recursivelyTranslate(splitToUnion(left, leftOnly).no(), context);
        Term noRightOnlyTerm = recursivelyTranslate(splitToUnion(right, rightOnly).no(), context);
        List<Term> intersectionConjuncts = PreprocessUtil.splitResolvant(intersection, sortPolicy).stream()
                .map(coveringExpr -> pushdown(left.intersect(coveringExpr).equal(right.intersect(coveringExpr))))
                .map(expr -> recursivelyTranslate(expr, context))
                .collect(Collectors.toList());

        intersectionConjuncts.add(noLeftOnlyTerm);
        intersectionConjuncts.add(noRightOnlyTerm);
        return Term.mkAnd(intersectionConjuncts);
    }

    @Override
    public Term translate(ExprUnary expr, TranslationContext context) {
        if (expr.op == ExprUnary.Op.CARDINALITY) {
            return translateCard(expr.sub, context);
        } else if (expr.op == ExprUnary.Op.SOME || expr.op == ExprUnary.Op.NO) {
            return translateSomeNoExpr(expr.op, expr.sub, context);
        }
        return null;
    }

    // [[#e]] := [[#(e&A)]] + [[#(e&B)]] when resolvant(e) = {A, B}
    private Term translateCard(Expr expr, TranslationContext context) {
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (resolvant.isNone() || resolvant.isDefinite()) return null;

        return recursivelyTranslate(pushdown(splitToUnion(expr, resolvant).cardinality()), context);
    }

    private Term translateSomeNoExpr(ExprUnary.Op op, Expr expr, TranslationContext context) {
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (resolvant.isNone() || resolvant.isDefinite()) return null;

        Expr split = splitToUnion(expr, resolvant);
        Expr opSplit;
        if (op == ExprUnary.Op.SOME) {
            opSplit = split.some();
        } else { // no
            opSplit = split.no();
        }
        return recursivelyTranslate(pushdown(opSplit), context);
    }

    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
        if (expr.op != ExprBinary.Op.JOIN) return null;

        // Push down join to avoid sort merging errors
        Pushdown pushdown = pushdownWithResult(expr);
        if (pushdown.effective) { // only if effective to avoid infinite recursion
            return recursivelyTranslate(ExprElementOf.make(tuple, pushdown.result), context);
        }

        // TODO - maybe something with & to avoid sort merging errors here
        return null;
    }

    @Override
    public Term translate(ExprQt expr, TranslationContext context) {
        if (expr.op != ExprQt.Op.ALL && expr.op != ExprQt.Op.NO && expr.op != ExprQt.Op.SOME) return null;

        // do the anti-merge preprocessing online
        Expr preprocessed = AntiMergePreprocessor.preprocessFormula(
                expr, context.getVarMappingContext(), sortPolicy, nameGenerator);
        if (preprocessed != expr) {
            return recursivelyTranslate(preprocessed, context);
        }
        return null;
    }
}
