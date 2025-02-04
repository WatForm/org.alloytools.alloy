package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.Macro;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

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

    /**
     * Naturally recurses over the Alloy AST and builds up a copy of it.
     * Also keeps a VarMappingContext, but maintains only term/let mappings, not Fortress var mappings!
     * Extend this to perform a transformation over the Alloy AST.
     */
    static class AlloyASTMapper extends FortressVisitReturn<Expr> {

        protected final VarMappingContext varMappingContext = new VarMappingContext();
        protected final SortPolicy sortPolicy;

        public AlloyASTMapper(SortPolicy sortPolicy) {
            this.sortPolicy = sortPolicy;
        }

        private List<Expr> visitAll(List<Expr> exprs) {
            return exprs.stream().map(this::visitThis).collect(Collectors.toList());
        }

        private List<Decl> visitDecls(List<Decl> decls) {
            return decls.stream()
                    .map(decl -> new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar, decl.names,
                            visitThis(decl.expr)))
                    .collect(Collectors.toList());
        }

        @Override
        public Expr visit(ExprBinary x) throws Err {
            return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            return ExprList.make(x.pos, x.closingBracket, x.op, visitAll(x.args));
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            return ExprCall.make(x.pos, x.closingBracket, x.fun, visitAll(x.args), x.extraWeight);
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return ExprITE.make(x.pos, visitThis(x.cond), visitThis(x.left), visitThis(x.right));
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return ExprLet.make(x.pos, x.var, visitThis(x.expr), visitLetSub(x));
        }

        protected final Expr visitLetSub(ExprLet x) {
            varMappingContext.addLetMapping(x.var.label, x.expr);
            try {
                return visitThis(x.sub);
            } finally {
                varMappingContext.removeMapping(x.var.label);
            }
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            return x.op.make(x.pos, x.closingBracket, visitDecls(x.decls), visitQuantifierSub(x.decls, x.sub));
        }

        // TODO reduce duplication with ContextVisitReturn
        private static final String PLACEHOLDER_BOUND_VAR_PREFIX = "%boundPlaceholderVar%";

        private Var getPlaceholderBoundVar(Sort sort) {
            // use the same one for each sort
            return Term.mkVar(PLACEHOLDER_BOUND_VAR_PREFIX + sort.name());
        }

        protected final Expr visitQuantifierSub(List<Decl> decls, Expr sub) {
            // TODO reduce duplication with ContextVisitReturn
            List<String> varNamesAdded = new ArrayList<>();
            List<Var> placeholderBoundVars = new ArrayList<>();
            try {
                for (Decl decl : decls) {
                    for (ExprHasName name : decl.names) {
                        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(decl.expr, varMappingContext);
                        if (resolvant.isNone()) {
                            // If the resolvant is none, **do not visit any further variables or add them to the context**.
                            // This is because we always short-circuit any quantifiers with none sorts, so we do not
                            // recurse into them. This is necessary for Portus to work with e.g. "some x: none | ...".
                            // THIS MAY CAUSE BUGS! THIS IS A LIKELY SPOT FOR ODD BEHAVIOUR!
                            return visitThis(sub);
                        }

                        if (!resolvant.isDefinite()) {
                            throw new ErrorNoPortusSupport("Quantifier decl expression must have definite sorts!");
                        }
                        if (resolvant.arity() > 1) {
                            throw new ErrorNoPortusSupport("Portus only supports unary quantifier decl expressions!");
                        }
                        Sort sort = resolvant.getDefiniteSorts().get(0);
                        Var placeholderBoundVar = getPlaceholderBoundVar(sort);
                        varMappingContext.addTermMapping(name.label, new AnnotatedTerm(placeholderBoundVar.of(sort)));
                        varMappingContext.addFortressVar(placeholderBoundVar.of(sort));
                        varNamesAdded.add(name.label);
                        placeholderBoundVars.add(placeholderBoundVar);
                    }
                }
                return visitThis(sub);
            } finally {
                // remove the var mappings in reverse order
                for (int i = varNamesAdded.size() - 1; i >= 0; i--) {
                    varMappingContext.removeMapping(varNamesAdded.get(i));
                }
                for (int i = placeholderBoundVars.size() - 1; i >= 0; i--) {
                    varMappingContext.removeFortressVar(placeholderBoundVars.get(i));
                }
            }
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            return x.op.make(x.pos, visitThis(x.sub));
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            // *don't* recurse into variables from let mappings
            return x;
        }

        @Override
        public Expr visit(Sig x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprElementOf x) throws Err {
            return ExprElementOf.make(x.tuple, visitThis(x.sub));
        }

        @Override
        public Expr visit(Func x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Assert x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Macro macro) throws Err {
            return macro;
        }
    }

}
