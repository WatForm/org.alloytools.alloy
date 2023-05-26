package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Value;
import fortress.operations.Substituter;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

// TODO: test that integers work with this
final class BruteForceEvaluator implements Evaluator {

    private final Translator translator;

    public BruteForceEvaluator(Translator translator) {
        this.translator = translator;
    }

    @Override
    public TupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        if (expr.type().is_bool) {
            // A formula - just check it and return the boolean
            boolean result = evaluateBooleanExpr(expr, solution, context);
            return TupleSet.singleton(result ? Term.mkTop() : Term.mkBottom());
        }

        return bruteForceEval(expr, solution, context);
    }

    private boolean evaluateBooleanExpr(Expr expr, FortressSolution solution, TranslationContext context) {
        // Translate to Fortress - copy the translation context to avoid any modifications
        TranslationContext contextCopy = new TranslationContext(context);
        Term fortressTerm = translator.translate(expr, contextCopy);
        return solution.evaluateFormula(fortressTerm);
    }

    private TupleSet bruteForceEval(Expr expr, FortressSolution solution, TranslationContext context) {
        // Manually evaluate {(x1,...,xn) : sorts | [[(x1,...,xn) \in expr]]}
        Set<List<Value>> tupleSet = new HashSet<>();
        List<Sort> sorts = context.sortPolicy.getAllSorts();
        int arity = expr.type().arity();

        // Optimization: if we can determine that some positions can only have atoms of a certain sort,
        // only try values from that sort
        List<Sort> exprSorts = context.sortPolicy.getMinimalExprSorts(expr, context);
        if (exprSorts == null) {
            // if we couldn't get the sorts for some reason, just try all sorts
            exprSorts = Collections.nCopies(arity, null);
        }
        if (arity != exprSorts.size()) {
            throw new ErrorFatal("Evaluating " + expr + ": type arity " + arity + " conflicts with determined arity "
                    + exprSorts.size());
        }
        List<List<Sort>> sortsPerPosition = exprSorts.stream()
                .map(sort -> SortPolicy.isSortDefinite(sort) ? Collections.singletonList(sort) : sorts)
                .collect(Collectors.toList());

        cartesianProduct(sortsPerPosition).forEach(sortCombo -> {
            // Use this trick to avoid calling translate() for every combination of atoms:
            // for (v1,...,vn) \in expr, make vars x1,...,xn and translate [[(x1,...,xn) \in expr]]
            // and then substitute xi->vi for i=1..n.
            List<AnnotatedVar> vars = sortCombo.stream()
                    .map(sort -> Term.mkVar(context.nameGenerator.freshName("var_" + sort)).of(sort))
                    .collect(Collectors.toList());

            TranslationContext contextCopy = new TranslationContext(context);
            Expr inExpr = ExprElementOf.make(TermTuple.fromVars(vars), expr);
            Term formula = translator.translate(inExpr, contextCopy);

            List<List<Value>> sortAtoms = sortCombo.stream()
                    .map(solution::getSortAtoms)
                    .collect(Collectors.toList());
            cartesianProduct(sortAtoms).forEach(tuple -> {
                // Substitute for the values we want to evaluate
                Term substitutedFormula = formula;
                for (int i = 0; i < tuple.size(); i++) {
                    substitutedFormula = Substituter.apply(
                            vars.get(i).variable(), tuple.get(i), substitutedFormula, contextCopy.nameGenerator);
                }

                boolean inSet = solution.evaluateFormula(substitutedFormula);
                if (inSet) {
                    tupleSet.add(tuple);
                }
            });
        });

        return new TupleSet(tupleSet, arity);
    }

    // Compute the Cartesian product of the lists recursively and lazily
    private <T> Stream<? extends List<T>> cartesianProduct(List<List<T>> lists) {
        if (lists.size() == 0) {
            // Singleton list with just ()
            return Stream.of(new ArrayList<>());
        } else {
            // Compute product(lists[:-1]) x lists[-1]
            Stream<? extends List<T>> prev = cartesianProduct(lists.subList(0, lists.size() - 1));
            List<T> last = lists.get(lists.size() - 1);
            return prev.flatMap(tuple -> last.stream().map(value -> {
                List<T> addedTuple = new ArrayList<>(tuple);
                addedTuple.add(value);
                return addedTuple;
            }));
        }
    }

}
