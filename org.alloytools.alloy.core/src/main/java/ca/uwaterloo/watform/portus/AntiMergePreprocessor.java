package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Preprocesses an Alloy formula to try and avoid having to merge sorts in the sort policy.
 * For example, if the sort policy assigns resolvant(e) = {(A), (Int)}, then we replace:
 *   all x: e | f  -->  (all x: e&A | f) && (all x: e&Int | f)
 * TODO still needs optimized
 */
public final class AntiMergePreprocessor implements Preprocessor {

    private final NameGenerator nameGenerator;

    public AntiMergePreprocessor(NameGenerator nameGenerator) {
        this.nameGenerator = nameGenerator;
    }

    /** Run the preprocessor on the command. */
    @Override
    public AlloyProblem preprocess(AlloyProblem problem) {
        ScopeComputer scoper = problem.makeScopeComputer();
        // Use the type sort policy because it's fast and we make a lot of calls, and we assume no sig hierarchy
        SortPolicy sortPolicy = new TypeSortPolicy(problem.getSigs(), scoper, nameGenerator);

        // use one visitor for everything to keep caches
        VarMappingContext varMappingContext = new VarMappingContext();
        PreprocessVisitor visitor = new PreprocessVisitor(
                varMappingContext, sortPolicy, nameGenerator, new HashMap<>());

        // preprocess sig facts
        for (Sig sig : problem.getSigs()) {
            if (sig.builtin) continue;
            List<Expr> facts = new ArrayList<>();
            sig.getFacts().forEach(facts::add);
            if (facts.isEmpty()) continue;

            // Add "this: one sig" to the mapping context
            Sort sigSort = sortPolicy.getSort(sig);
            Var thisVar = Term.mkVar(nameGenerator.freshName("%placeholderThis"));
            varMappingContext.addTermMapping("this", new AnnotatedTerm(thisVar, sigSort));
            varMappingContext.addFortressVar(thisVar, sigSort);

            try {
                sig.resetFacts();
                for (Expr fact : facts) {
                    sig.addFact(visitor.visitThis(fact));
                }
            } finally {
                varMappingContext.removeMapping("this");
                varMappingContext.removeFortressVar(thisVar);
            }
        }

        Expr newFormula = visitor.visitThis(problem.getFormula());
        System.out.println("Preprocessing finished!");
        return problem.withFormula(newFormula);
    }

    public static Expr preprocessFormula(Expr formula, VarMappingContext context, SortPolicy sortPolicy,
                                         NameGenerator nameGenerator) {
        PreprocessVisitor visitor = new PreprocessVisitor(context, sortPolicy, nameGenerator, new HashMap<>());
        return visitor.visitThis(formula);
    }

    private static final class PreprocessVisitor extends NaturalRecursion.AlloyASTMapper {

        private final NameGenerator nameGenerator;

        private final Map<Pair<Func, List<SortResolvant>>, Func> funcCache;

        public PreprocessVisitor(VarMappingContext varMappingContext, SortPolicy sortPolicy,
                                 NameGenerator nameGenerator, Map<Pair<Func, List<SortResolvant>>, Func> funcCache) {
            super(sortPolicy, varMappingContext);
            this.nameGenerator = nameGenerator;
            this.funcCache = funcCache;
        }

        @Override
        protected Expr recurse(Expr expr, VarMappingContext newVarMappingContext) {
            return new PreprocessVisitor(newVarMappingContext, sortPolicy, nameGenerator, funcCache).visitThis(expr);
        }

        // TODO prune!
        @Override
        public Expr visit(ExprQt x) throws Err {
            if (x.op != ExprQt.Op.ALL && x.op != ExprQt.Op.SOME && x.op != ExprQt.Op.NO
                && x.op != ExprQt.Op.COMPREHENSION && x.op != ExprQt.Op.SUM) {
                return super.visit(x);
            }

            // Desugar away the "disjoint" keyword, which we don't support here.
            Expr desugared = x.desugar();
            if (desugared != x) {
                return visitThis(desugared);
            }

            List<List<Decl>> newQuantifierDecls = generateQuantifierDecls(x.decls);
            List<Expr> newQuantifiers = newQuantifierDecls.stream()
                    .map(decls -> x.op.make(x.pos, x.closingBracket, decls, visitQuantifierSub(decls, x.sub)))
                    .collect(Collectors.toList());

            // Combine them with an appropriate boolean operator for the quantifier
            // TODO: one, lone
            if (x.op == ExprQt.Op.ALL || x.op == ExprQt.Op.NO) {
                return ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, newQuantifiers);
            } else if (x.op == ExprQt.Op.SOME) {
                return ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, newQuantifiers);
            } else if (x.op == ExprQt.Op.COMPREHENSION) {
                return newQuantifiers.stream().reduce(Expr::plus)
                        .orElse(PortusUtil.noneOfArity(x.type().arity()));
            } else { // sum
                return newQuantifiers.stream().reduce(Expr::iplus).orElse(ExprConstant.makeNUMBER(0));
            }
        }

        private List<List<Decl>> generateQuantifierDecls(List<Decl> decls) {
            // Do it recursively so we can add to the context each time
            // Worst-case exponential in the number of decls but that's okay
            if (decls.isEmpty()) return Collections.singletonList(new ArrayList<>());

            Decl decl = decls.get(0);
            List<Decl> otherDecls = decls.subList(1, decls.size());

            List<Expr> splitExprs = PreprocessUtil.splitExpr(decl.expr, sortPolicy, varMappingContext).stream()
                    .map(this::visitThis)
                    .collect(Collectors.toList());
            List<Sort> splitExprSorts = splitExprs.stream().map(splitExpr -> {
                // Find the sort of the dummy variable to add to the context
                SortResolvant resolvant = sortPolicy.getMinimalExprSorts(splitExpr, varMappingContext);
                if (resolvant.isNone()) {
                    return null; // will be filtered later
                }
                if (!resolvant.isDefinite()) {
                    throw new ErrorFatal("Internal Portus error: split expr does not have definite sorts!");
                }
                List<Sort> sorts = resolvant.getDefiniteSorts();
                if (sorts.size() != 1) {
                    throw new ErrorNoPortusSupport("Portus does not support quantifying over arity > 1!");
                }
                return sorts.get(0);
            }).collect(Collectors.toList());

            // Remove any exprs that resolved to none (null sorts above)
            List<Expr> splitExprsFiltered = new ArrayList<>();
            for (int i = 0; i < splitExprs.size(); i++) {
                if (splitExprSorts.get(i) != null) {
                    splitExprsFiltered.add(splitExprs.get(i));
                }
            }
            splitExprSorts.removeIf(Objects::isNull);

            return generateQuantifierDeclsForNames(decl, decl.names, splitExprsFiltered, splitExprSorts, otherDecls);
        }

        private List<List<Decl>> generateQuantifierDeclsForNames(
                Decl decl, List<? extends ExprHasName> names, List<Expr> splitExprs, List<Sort> splitExprSorts,
                List<Decl> otherDecls) {
            if (names.isEmpty()) {
                return generateQuantifierDecls(otherDecls);
            }

            ExprHasName name = names.get(0);
            List<? extends ExprHasName> otherNames = names.subList(1, names.size());

            List<List<Decl>> result = new ArrayList<>();
            for (int i = 0; i < splitExprs.size(); i++) {
                Var dummy = Term.mkVar(nameGenerator.freshName("antiMergeDummy"));
                try {
                    varMappingContext.addFortressVar(dummy, splitExprSorts.get(i));
                    varMappingContext.addTermMapping(name.label, new AnnotatedTerm(dummy, splitExprSorts.get(i)));

                    Decl newDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar,
                            Collections.singletonList(name), splitExprs.get(i));
                    List<List<Decl>> newDeclLists = generateQuantifierDeclsForNames(
                            decl, otherNames, splitExprs, splitExprSorts, otherDecls);

                    // prepend the new decl to each
                    for (List<Decl> declList : newDeclLists) {
                        declList.add(0, newDecl);
                    }
                    result.addAll(newDeclLists);
                } finally {
                    varMappingContext.removeFortressVar(dummy);
                    varMappingContext.removeMapping(name.label);
                }
            }
            return result;
        }

        // compute op(a,b) but leave off a or b if none
        private Expr pruneUnionBinOp(ExprBinary.Op op, Expr ifNone, Expr a, Expr b) {
            SortResolvant resolvantA = sortPolicy.getMinimalExprSorts(a, varMappingContext);
            SortResolvant resolvantB = sortPolicy.getMinimalExprSorts(b, varMappingContext);
            if (resolvantA.isNone() && resolvantB.isNone()) {
                return ifNone;
            } else if (resolvantA.isNone()) {
                return pushdownShallow(b);
            } else if (resolvantB.isNone()) {
                return pushdownShallow(a);
            } else {
                return op.make(null, null, pushdownShallow(a), pushdownShallow(b));
            }
        }

        private Expr pruneUnion(Expr a, Expr b) {
            return pruneUnionBinOp(ExprBinary.Op.PLUS, PortusUtil.noneOfArity(a.type().arity()), a, b);
        }

        private Expr pruneMinus(Expr a, Expr b) {
            SortResolvant resolvantA = sortPolicy.getMinimalExprSorts(a, varMappingContext);
            SortResolvant resolvantB = sortPolicy.getMinimalExprSorts(b, varMappingContext);
            if (resolvantA.isNone()) {
                return PortusUtil.noneOfArity(resolvantA.arity());
            } else if (resolvantB.isNone()) {
                return pushdownShallow(a);
            } else {
                return pushdownShallow(a).minus(pushdownShallow(b));
            }
        }

        // return expr, but none if expr has a none sort resolvant
        private Expr prune(Expr expr) {
            if (sortPolicy.getMinimalExprSorts(expr, varMappingContext).isNone()) {
                return PortusUtil.noneOfArity(expr.type().arity());
            }
            return expr;
        }

        private Expr pushdownShallow(Expr expr) {
            if (expr instanceof ExprBinary) {
                ExprBinary x = (ExprBinary) expr;
                if (x.left instanceof ExprBinary && ((ExprBinary) x.left).op == ExprBinary.Op.PLUS) {
                    ExprBinary leftUnion = (ExprBinary) x.left;
                    if (x.op == ExprBinary.Op.INTERSECT) {
                        // (a+b)&c -> a&c + b&c
                        return pruneUnion(leftUnion.left.intersect(x.right), leftUnion.right.intersect(x.right));
                    } else if (x.op == ExprBinary.Op.JOIN) {
                        // (a+b).c -> a.c + b.c
                        return pruneUnion(leftUnion.left.join(x.right), leftUnion.right.join(x.right));
                    } else if (x.op == ExprBinary.Op.RANGE) {
                        // (a+b):>c -> a:>c + b:>c
                        return pruneUnion(leftUnion.left.range(x.right), leftUnion.right.range(x.right));
                    } else if (x.op == ExprBinary.Op.MINUS) {
                        // (a+b)-c -> (a-c) + (b-c)
                        // Note pushing down on the right isn't worth it b/c we only get a scalar when left is scalar!
                        return pruneUnion(leftUnion.left.minus(x.right), leftUnion.right.minus(x.right));
                    }
                } else if (x.left instanceof ExprBinary && ((ExprBinary) x.left).op == ExprBinary.Op.MINUS) {
                    ExprBinary leftMinus = (ExprBinary) x.left;
                    if (x.op == ExprBinary.Op.INTERSECT) {
                        // (a-b)&c -> a&c - b&c
                        return pruneMinus(leftMinus.left.intersect(x.right), leftMinus.right.intersect(x.right));
                    }
                }
                if (x.right instanceof ExprBinary && ((ExprBinary) x.right).op == ExprBinary.Op.PLUS) {
                    ExprBinary rightUnion = (ExprBinary) x.right;
                    if (x.op == ExprBinary.Op.INTERSECT) {
                        // a&(b+c) -> a&b + a&c
                        return pruneUnion(x.left.intersect(rightUnion.left), x.left.intersect(rightUnion.right));
                    } else if (x.op == ExprBinary.Op.JOIN) {
                        // a.(b+c) -> a.b + a.c
                        return pruneUnion(x.left.join(rightUnion.left), x.left.join(rightUnion.right));
                    } else if (x.op == ExprBinary.Op.DOMAIN) {
                        // a<:(b+c) -> a<:b + a<:c
                        return pruneUnion(x.left.domain(rightUnion.left), x.left.domain(rightUnion.right));
                    } else if (x.op == ExprBinary.Op.ARROW) {
                        // a->(b+c) -> a->b + a->c
                        // Note pushing down on the left isn't worth it b/c we only get a scalar when right is scalar!
                        return pruneUnion(x.op.make(null, null, x.left, rightUnion.left),
                                x.op.make(null, null, x.left, rightUnion.right));
                    }
                } else if (x.right instanceof ExprBinary && ((ExprBinary) x.right).op == ExprBinary.Op.MINUS) {
                    ExprBinary rightMinus = (ExprBinary) x.right;
                    if (x.op == ExprBinary.Op.INTERSECT) {
                        // a&(b-c) -> a&b - a&c
                        return pruneMinus(x.left.intersect(rightMinus.left), x.left.intersect(rightMinus.right));
                    }
                }
                if (x.op == ExprBinary.Op.JOIN) {
                    return visitJoin(x.left, x.right);
                }
                return x;
            } else if (expr instanceof ExprUnary) {
                ExprUnary x = (ExprUnary) expr;
                if (x.sub instanceof ExprBinary && ((ExprBinary) x.sub).op == ExprBinary.Op.PLUS) {
                    ExprBinary subUnion = (ExprBinary) x.sub;
                    if (x.op == ExprUnary.Op.TRANSPOSE) {
                        // ~(a+b) -> ~a + ~b
                        return pruneUnion(subUnion.left.transpose(), subUnion.right.transpose());
                    } else if (x.op == ExprUnary.Op.CARDINALITY) {
                        // #(a+b) -> plus[#a, #b]
                        return pruneUnionBinOp(ExprBinary.Op.IPLUS, ExprConstant.ZERO,
                                subUnion.left.cardinality(), subUnion.right.cardinality());
                    } else if (x.op == ExprUnary.Op.SOME) {
                        // some (a+b) -> (some a) or (some b)
                        return pushdownShallow(subUnion.left.some())
                                .or(pushdownShallow(subUnion.right.some()));
                    } else if (x.op == ExprUnary.Op.NO) {
                        // no (a+b) -> (no a) and (no b)
                        return pushdownShallow(subUnion.left.no())
                                .and(pushdownShallow(subUnion.right.no()));
                    }
                } else if (x.op == ExprUnary.Op.ONEOF || x.op == ExprUnary.Op.LONEOF
                        || x.op == ExprUnary.Op.SOMEOF || x.op == ExprUnary.Op.SETOF
                        || x.op == ExprUnary.Op.EXACTLYOF) {
                    // Recurse these just to allow using this method on "one x" in decl exprs
                    return x.op.make(null, pushdownShallow(x.sub));
                }
                return x;
            }
            return expr;
        }

        @Override
        public Expr visit(ExprBinary x) throws Err {
            // TODO consider further pruning if one of these resolves to none
            Expr left = visitThis(x.left);
            Expr right = visitThis(x.right);

            if (x.op == ExprBinary.Op.IN) {
                return visitIn(left, right);
            } else if (x.op == ExprBinary.Op.EQUALS) {
                return visitEq(left, right);
            } else if (x.op == ExprBinary.Op.NOT_EQUALS) {
                return visitEq(left, right).not();
            }

            return pushdownShallow(x.op.make(null, null, left, right));
        }

        // e1 in e2 --> (e1&A in e2&A) and (e1&B in e2&B) where resolvant(e1) = {A, B}
        private Expr visitIn(Expr left, Expr right) {
            SortResolvant resolvant = sortPolicy.getMinimalExprSorts(left, varMappingContext);
            if (resolvant.isNone()) {
                return ExprConstant.TRUE;
            } else if (resolvant.isDefinite()) {
                // left in (right & covering(left))
                Expr coveringExpr = PreprocessUtil.splitResolvant(resolvant, sortPolicy).get(0);
                return left.in(pushdownShallow(prune(right.intersect(coveringExpr))));
            }

            // TODO prune?
            // TODO pushdownShallow here ok?
            return PreprocessUtil.splitResolvant(resolvant, sortPolicy).stream()
                    .map(cover -> pushdownShallow(left.intersect(cover))
                            // TODO maybe don't need to prune, instead compute right's sort resolvant directly (faster)
                            .in(pushdownShallow(prune(right.intersect(cover)))))
                    .reduce(Expr::and)
                    .orElse(ExprConstant.TRUE);
        }

        // e1 = e2 --> (no e1&A) and (e1&B = e2&B) and (no e2&C) where resolvant(e1) = {A,B}, resolvant(e2) = {B,C}
        private Expr visitEq(Expr left, Expr right) {
            SortResolvant leftResolvant = sortPolicy.getMinimalExprSorts(left, varMappingContext);
            SortResolvant rightResolvant = sortPolicy.getMinimalExprSorts(right, varMappingContext);
            if (leftResolvant.isNone() && rightResolvant.isNone()) {
                return ExprConstant.TRUE;
            } else if (leftResolvant.isNone()) {
                return right.no();
            } else if (rightResolvant.isNone()) {
                return left.no();
            }
            SortResolvant leftOnlyRes = leftResolvant.difference(rightResolvant);
            SortResolvant rightOnlyRes = rightResolvant.difference(leftResolvant);
            SortResolvant intersectionRes = leftResolvant.intersection(rightResolvant);

            // TODO pushdownShallow here ok?
            List<Expr> leftOnly = PreprocessUtil.splitResolvant(leftOnlyRes, sortPolicy).stream()
                    .map(cover -> pushdownShallow(left.intersect(cover).no()))
                    .collect(Collectors.toList());
            List<Expr> rightOnly = PreprocessUtil.splitResolvant(rightOnlyRes, sortPolicy).stream()
                    .map(cover -> pushdownShallow(right.intersect(cover).no()))
                    .collect(Collectors.toList());
            List<Expr> intersection = PreprocessUtil.splitResolvant(intersectionRes, sortPolicy).stream()
                    .map(cover -> pushdownShallow(left.intersect(cover))
                            .equal(pushdownShallow(right.intersect(cover))))
                    .collect(Collectors.toList());

            intersection.addAll(leftOnly);
            intersection.addAll(rightOnly);
            return intersection.stream().reduce(Expr::and).orElse(ExprConstant.TRUE);
        }

        // e1.e2 --> (e1&(univ->A)).e2 + (e1&(univ->B)).e2 where middle column has sorts {A, B}
        // (could also do vice versa)
        private Expr visitJoin(Expr left, Expr right) {
            SortResolvant leftResolvant = sortPolicy.getMinimalExprSorts(left, varMappingContext);
            SortResolvant rightResolvant = sortPolicy.getMinimalExprSorts(right, varMappingContext);
            if (leftResolvant.isNone() || rightResolvant.isNone() || leftResolvant.join(rightResolvant).isNone()) {
                return PortusUtil.noneOfArity(leftResolvant.arity() + rightResolvant.arity() - 2);
            }

            Set<Sort> middleColumn = SetOps.intersection(
                    leftResolvant.getSortsInColumn(leftResolvant.arity() - 1),
                    rightResolvant.getSortsInColumn(0));
            if (middleColumn.size() <= 1) {
                return left.join(right); // don't bother
            }

            return middleColumn.stream()
                    .map(sortPolicy::getCoveringExpr)
                    .map(cover -> PortusUtil.univOfArity(leftResolvant.arity() - 1).product(cover))
                    .map(wholeCover -> pushdownShallow(left.intersect(wholeCover).join(right)))
                    .reduce(Expr::plus)
                    .orElse(PortusUtil.noneOfArity(leftResolvant.arity() + rightResolvant.arity() - 1));
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            Expr sub = visitThis(x.sub);
            return pushdownShallow(x.op.make(null, sub));
        }

        @Override
        public Func visitFunc(Func x, List<Expr> args) throws Err {
            // Lazily split into one func per sort resolvant of the arguments
            // We can't split sort resolvants because we don't know how to combine them, so hopefully this
            // doesn't leave too much sort merging!
            List<SortResolvant> resolvants = args.stream()
                    .map(arg -> sortPolicy.getMinimalExprSorts(arg, varMappingContext))
                    .collect(Collectors.toList());
            Pair<Func, List<SortResolvant>> cacheKey = new Pair<>(x, resolvants);

            Func cached = funcCache.get(cacheKey);
            if (cached != null) {
                return cached;
            }

            // Split by using the covering expressions of the resolvants as the decl expressions
            List<Decl> splitDecls = new ArrayList<>(x.decls.size());
            int arg = 0;
            for (Decl decl : x.decls) {
                for (ExprHasName name : decl.names) {
                    Expr coveringExpr = sortPolicy.getCoveringExpr(resolvants.get(arg));
                    Decl newDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar,
                            Collections.singletonList(name), coveringExpr);
                    splitDecls.add(newDecl);
                    arg++;
                }
            }

            Expr returnDecl = x.isPred ? null : x.returnDecl; // so Alloy still thinks it's a pred if so
            String splitFuncLabel = nameGenerator.freshName(x.label);
            Func splitFunc = new Func(x.pos, x.isPrivate, x.labelPos,
                    splitFuncLabel, splitDecls, returnDecl, x.getBody());

            // Preprocess this function too
            Func preprocessed = super.visitFunc(splitFunc, args);
            funcCache.put(cacheKey, preprocessed);
            return preprocessed;
        }

    }

}
