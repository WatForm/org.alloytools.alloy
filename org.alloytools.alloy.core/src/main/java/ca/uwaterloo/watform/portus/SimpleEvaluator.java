package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.Term;
import fortress.msfol.Value;

/**
 * An evaluator handling nodes that require no state to evaluate, such as unions and intersections.
 */
// TODO integers, either here or in a dedicated evaluator
final class SimpleEvaluator implements Evaluator {

    private final Evaluator rootEvaluator;

    public SimpleEvaluator(Evaluator rootEvaluator) {
        this.rootEvaluator = rootEvaluator;
    }

    private ValueTupleSet evaluate(ExprBinary expr, FortressSolution solution, TranslationContext context) {
        switch (expr.op) {
            case PLUS:
                return rootEvaluator.evaluate(expr.left, solution, context).union(
                        rootEvaluator.evaluate(expr.right, solution, context));
            case INTERSECT:
                return rootEvaluator.evaluate(expr.left, solution, context).intersection(
                        rootEvaluator.evaluate(expr.right, solution, context));
            case MINUS:
                return rootEvaluator.evaluate(expr.left, solution, context).difference(
                        rootEvaluator.evaluate(expr.right, solution, context));
            case ARROW:
                return rootEvaluator.evaluate(expr.left, solution, context).cartesianProduct(
                        rootEvaluator.evaluate(expr.right, solution, context));
            case JOIN:
                return rootEvaluator.evaluate(expr.left, solution, context).join(
                        rootEvaluator.evaluate(expr.right, solution, context));
            case PLUSPLUS:
                return rootEvaluator.evaluate(expr.left, solution, context).override(
                        rootEvaluator.evaluate(expr.right, solution, context));
        }
        return null;
    }

    private ValueTupleSet evaluate(ExprUnary expr, FortressSolution solution, TranslationContext context) {
        switch (expr.op) {
            case TRANSPOSE:
                return rootEvaluator.evaluate(expr.sub, solution, context).transpose();
            case CLOSURE:
                return rootEvaluator.evaluate(expr.sub, solution, context).transitiveClosure();
                // TODO: RCLOSURE is problematic due to inclusion of iden
                // TODO: cardinality along with integers
            case NOOP:
            case CAST2INT:
            case CAST2SIGINT:
                // Noops: give the whole evaluator stack a chance to run through it
                return rootEvaluator.evaluate(expr.sub, solution, context);
        }
        return null;
    }

    private ValueTupleSet evaluate(ExprITE expr, FortressSolution solution, TranslationContext context) {
        ValueTupleSet condition = rootEvaluator.evaluate(expr.cond, solution, context);
        if (!condition.isPureBoolean()) {
            throw new ErrorFatal("If-then-else condition did not evaluate to a boolean!");
        }
        return condition.getPureBoolean()
                ? rootEvaluator.evaluate(expr.left, solution, context)
                : rootEvaluator.evaluate(expr.right, solution, context);
    }

    private ValueTupleSet evaluate(ExprConstant expr) {
        switch (expr.op) {
            case TRUE:
                return ValueTupleSet.singleton(Term.mkTop());
            case FALSE:
                return ValueTupleSet.singleton(Term.mkBottom());
            case EMPTYNESS:
                // Don't deal with none at the moment because it breaks TupleSet's assumption that every set has
                // exactly one arity. We probably don't have to deal with it since A4SolutionWriter won't give us nones?
                throw new ErrorNoPortusSupport("Portus cannot evaluate none currently!");
        }
        return null;
    }

    private ValueTupleSet evaluate(ExprLet expr, FortressSolution solution, TranslationContext context) {
        // It'd be more efficient to evaluate expr.expr once instead of every time the var is used, but so be it.
        context.addLetMapping(expr.var.label, expr.expr);
        try {
            return rootEvaluator.evaluate(expr.sub, solution, context);
        } finally {
            context.removeMapping(expr.var.label);
        }
    }

    private ValueTupleSet evaluate(ExprCall expr, FortressSolution solution, TranslationContext context) {
        context.addLetMappingsFromCall(expr);
        try {
            return rootEvaluator.evaluate(expr.fun.getBody(), solution, context);
        } finally {
            context.removeLetMappingsFromCall(expr);
        }
    }

    private ValueTupleSet evaluate(ExprVar var, FortressSolution solution, TranslationContext context) {
        if (context.hasLetMapping(var.label)) {
            VarMappingContext.LetContext letContext = context.getLetMapping(var.label);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return rootEvaluator.evaluate(letContext.getExpr(), solution, context);
            } finally {
                letContext.resetMapping();
            }
        } else if (context.hasTermMapping(var.label)) {
            // evaluate it in the solution
            AnnotatedTerm term = context.getTermMapping(var.label);
            assert term != null;
            Value result = solution.evaluateTerm(term.getTerm());
            return ValueTupleSet.singleton(result);
        }
        // Unknown - maybe someone else can deal with it
        return null;
    }

    @Override
    public ValueTupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        if (expr instanceof ExprBinary) {
            return evaluate((ExprBinary) expr, solution, context);
        } else if (expr instanceof ExprUnary) {
            return evaluate((ExprUnary) expr, solution, context);
        } else if (expr instanceof ExprITE) {
            return evaluate((ExprITE) expr, solution, context);
        } else if (expr instanceof ExprConstant) {
            return evaluate((ExprConstant) expr);
        } else if (expr instanceof ExprLet) {
            return evaluate((ExprLet) expr, solution, context);
        } else if (expr instanceof ExprCall) {
            return evaluate((ExprCall) expr, solution, context);
        } else if (expr instanceof ExprVar) {
            return evaluate((ExprVar) expr, solution, context);
        }
        return null;
    }

}
