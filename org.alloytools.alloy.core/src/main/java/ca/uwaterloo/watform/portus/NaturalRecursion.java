package ca.uwaterloo.watform.portus;

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

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;

/**
 * Functions for "naturally" recursing over an Alloy AST.
 */
final class NaturalRecursion {

    /**
     * Naturally recurse over expr's AST and combine the results.
     */
    public static <T> T accumulate(
            T initial, BinaryOperator<T> combiner, BiFunction<Expr, VarMappingContext, T> generator,
            Expr expr, SortPolicy sortPolicy, VarMappingContext varMappingContext) {
        return new ContextVisitReturn<T>(varMappingContext, sortPolicy) {
            @Override
            public T visit(ExprBinary x) throws Err {
                return combiner.apply(
                        generator.apply(x, varMappingContext),
                        combiner.apply(visitThis(x.left), visitThis(x.right)));
            }

            @Override
            public T visit(ExprList x) throws Err {
                return combiner.apply(generator.apply(x, varMappingContext), x.args.stream()
                        .map(this::visitThis)
                        .reduce(initial, combiner));
            }

            @Override
            public T visit(ExprCall x) throws Err {
                // note: run the combiner after substituting variables
                try {
                    varMappingContext.addLetMappingsFromCall(x);
                    return combiner.apply(generator.apply(x, varMappingContext), visitThis(x.fun.getBody()));
                } finally {
                    varMappingContext.removeLetMappingsFromCall(x);
                }
            }

            @Override
            public T visit(ExprConstant x) throws Err {
                return generator.apply(x, varMappingContext);
            }

            @Override
            public T visit(ExprITE x) throws Err {
                return combiner.apply(
                        generator.apply(x, varMappingContext),
                        combiner.apply(visitThis(x.cond), combiner.apply(visitThis(x.left), visitThis(x.right))));
            }

            @Override
            public T visit(ExprUnary x) throws Err {
                return combiner.apply(generator.apply(x, varMappingContext), visitThis(x.sub));
            }

            @Override
            public T visit(Sig x) throws Err {
                return generator.apply(x, varMappingContext);
            }

            @Override
            public T visit(Sig.Field x) throws Err {
                return combiner.apply(generator.apply(x, varMappingContext), visitThis(x.decl().expr));
            }

            @Override
            public T visit(ExprElementOf x) throws Err {
                return combiner.apply(generator.apply(x, varMappingContext), visitThis(x.sub));
            }

            @Override
            public T visitLet(ExprLet x) throws Err {
                // note: after substituting variables
                return combiner.apply(generator.apply(x, varMappingContext), visitThis(x.sub));
            }

            @Override
            public T visitQuantifier(ExprQt x, List<T> argResults, boolean anyArgNone) throws Err {
                // TODO: Technically, it is incorrect to ignore anyArgNone. But in the ways this function
                //  is currently used, it *should* be fine, because ExprVars are not important.
                //  More correct would be to completely ignore this term if anyArgNone is true, but then it's
                //  possible some other part of Portus recurses into the term and causes incorrect behaviour.
                return combiner.apply(combiner.apply(generator.apply(x, varMappingContext), visitThis(x.sub)),
                        argResults.stream().reduce(initial, combiner));
            }

            @Override
            public T visitQuantifierArg(Expr arg) throws Err {
                return visitThis(arg);
            }

            @Override
            public T visitVar(ExprVar x) throws Err {
                return generator.apply(x, varMappingContext);
            }

            @Override
            public T visit(Func x) throws Err {
                return initial;
            }

            @Override
            public T visit(Assert x) throws Err {
                return initial;
            }

            @Override
            public T visit(Macro macro) throws Err {
                return initial;
            }
        }.visitThis(expr);
    }

    /**
     * Naturally recurse over expr's AST and combine the results into a set.
     */
    public static <T> Set<T> accumulate(
            BiFunction<Expr, VarMappingContext, Set<T>> generator, Expr expr, SortPolicy sortPolicy,
            VarMappingContext varMappingContext) {
        return accumulate(new HashSet<>(), SetOps::union, generator, expr, sortPolicy, varMappingContext);
    }

}
