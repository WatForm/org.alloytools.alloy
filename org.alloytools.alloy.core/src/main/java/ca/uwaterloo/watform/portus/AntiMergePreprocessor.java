package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Preprocesses an Alloy formula to try and avoid having to merge sorts in the sort policy.
 * For example, if the sort policy assigns resolvant(e) = {(A), (Int)}, then we replace:
 *   all x: e | f  -->  (all x: e&A | f) && (all x: e&Int | f)
 */
final class AntiMergePreprocessor extends NaturalRecursion.AlloyASTMapper {

    public AntiMergePreprocessor(
            Iterable<Sig> allSigs, Command command, ModelInfo modelInfo, ScopeComputer scoper,
            NameGenerator nameGenerator) {
        super(PartitionSortPolicy.makeWithoutMergingSorts(
                new PortusStatistics(), allSigs, command, modelInfo, scoper, nameGenerator));
    }

    /** Run the preprocessor on the command. */
    public Command preprocess(Command command) {
        Expr newFormula = visitThis(command.formula);
        return new Command(
                command.pos, command.nameExpr, command.label, command.check, command.overall, command.bitwidth,
                command.maxseq, command.minprefix, command.maxprefix, command.expects, command.scope,
                command.additionalExactScopes, command.commandKeyword, newFormula, command.parent);
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        if (x.op != ExprQt.Op.ALL && x.op != ExprQt.Op.SOME && x.op != ExprQt.Op.NO) return super.visit(x);

        // Desugar away the "disjoint" keyword, which we don't support here.
        Expr desugared = x.desugar();
        if (desugared != x) {
            return visitThis(desugared);
        }

        // Worst case exponential in the number of decls, but that's okay
        // splitDeclLists[i] is the set of new decls that are generated for the ith decl
        // We then take the cartesian product of all of these to generate the set of new decl lists
        List<List<Decl>> splitDeclLists = new ArrayList<>();
        for (Decl decl : x.decls) {
            // one decl per name, even if they're combined in the original
            // case where this is required: "all a, b: univ | a in A and b in B" requires a in A, b in B simultaneously
            List<Expr> splitExprs = splitExpr(decl.expr);
            List<List<Decl>> splitDecls = decl.names.stream()
                    .map(name -> splitExprs.stream()
                            .map(expr -> new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar,
                                    Collections.singletonList(name), expr))
                            .collect(Collectors.toList()))
                    .collect(Collectors.toList());
            splitDeclLists.addAll(splitDecls);
        }

        // Take the cartesian product to generate the new quantifiers
        List<List<Decl>> newQuantifierDecls = SetOps.cartesianProduct(splitDeclLists);
        List<Expr> newQuantifiers = newQuantifierDecls.stream()
                .map(decls -> x.op.make(x.pos, x.closingBracket, decls, visitQuantifierSub(decls, x.sub)))
                .collect(Collectors.toList());

        // Combine them with an appropriate boolean operator for the quantifier
        // TODO: one, lone
        if (x.op == ExprQt.Op.ALL || x.op == ExprQt.Op.NO) {
            return ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, newQuantifiers);
        } else { // some
            return ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, newQuantifiers);
        }
    }

    // Split expr into multiple expressions with definite sorts.
    // E.g. if e has sort resolvant {A->A, B->C, Int->Int}, splitExpr(e) = {e&(A->A), e&(B->C), e&(Int->Int)}.
    private List<Expr> splitExpr(Expr expr) {
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

}
