package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;

@FunctionalInterface
interface Evaluator {

    TupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context);

}
