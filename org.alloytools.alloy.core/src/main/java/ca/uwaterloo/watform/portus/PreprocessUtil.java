package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

// TODO - actually not only for preprocessing, rename/move
final class PreprocessUtil {

    /**
     * Split expr into multiple expressions with definite sorts.
     * E.g. if e has sort resolvant {A->A, B->C, Int->Int}, splitExpr(e) = {e&(A->A), e&(B->C), e&(Int->Int)}.
     */
    public static List<Expr> splitExpr(Expr expr, SortPolicy sortPolicy, VarMappingContext varMappingContext) {
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, varMappingContext);
        if (resolvant.isDefinite() || resolvant.isNone()) {
            // Don't bother mutating for definite resolvants since it's fine, and none will be short-circuited
            return Collections.singletonList(expr);
        }

        // If there's a multiplicity like "one e" on the outside of expr, strip it and reapply on the outside.
        // This is because multiplicities like this are only legal in some locations.
        expr = expr.deNOP();
        ExprUnary.Op multOp = null;
        if (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            if (unary.op == ExprUnary.Op.ONEOF || unary.op == ExprUnary.Op.SOMEOF
                    || unary.op == ExprUnary.Op.LONEOF || unary.op == ExprUnary.Op.SETOF
                    || unary.op == ExprUnary.Op.EXACTLYOF) {
                multOp = unary.op;
                expr = unary.sub.deNOP();
            }
        }

        final Expr exprToSplit = expr; // to work around Java final requirement
        final ExprUnary.Op multOpToApply = multOp;
        return resolvant.stream().map(sorts -> {
            // e & (S1->S2->...->Sn)
            Expr coveringExpr = sorts.stream()
                    .map(sortPolicy::getCoveringExpr)
                    .reduce(Expr::product)
                    .orElse(ExprConstant.EMPTYNESS);
            Expr intersection = exprToSplit.intersect(coveringExpr);

            // reapply the multiplicity on the outside
            if (multOpToApply != null) {
                intersection = multOpToApply.make(exprToSplit.pos, intersection);
            }
            return intersection;
        }).collect(Collectors.toList());
    }

    /**
     * Split a sort resolvant into multiple expressions covering it.
     * E.g. if resolvant = {(A,B), (C,D)} then splitResolvant = {A->B, C->D}
     */
    public static List<Expr> splitResolvant(SortResolvant resolvant, SortPolicy sortPolicy) {
        return resolvant.stream().map(sorts -> sorts.stream()
                        .map(sortPolicy::getCoveringExpr)
                        .reduce(Expr::product)
                        .orElse(ExprConstant.EMPTYNESS))
                .collect(Collectors.toList());
    }

}
