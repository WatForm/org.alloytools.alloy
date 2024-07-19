package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * An optimization for transitive closure over expressions that can be interpreted as Fortress functions.
 * If f: S->S is a function from scalars to scalars, then roughly we can translate:
 *   [[(x,y) \in ^f]] := y = f(x) || y = f(f(x)) || y = f(f(f(x))) || ... || y = f^{|S|}(x)
 * This is implemented as follows. If castToScalar(x.e) = (e(x), guard(x)) for a fresh variable x, then
 *   [[(x,y) \in ^e]] := guard(x) && (y = e(x) || (guard(e(x)) && (y = e(e(x))
 *       || (... guard(e^{|S|-1}(x)) && y = e^{|S|}(x)))))
 *
 * Note that this is reliant upon x.f being a scalar - TODO recognize scalar-to-scalar functions.
 * A further possible optimization: if we know the maximum size of the range of the function and it's less than |S|,
 * we only have to go up to that size rather than |S|.
 */
final class ClosureOfScalarOptTranslator extends AbstractTranslator {

    private final ScalarCaster scalarCaster;
    private final SortPolicy sortPolicy;

    public ClosureOfScalarOptTranslator(
            Translator topLevel, ScalarCaster scalarCaster, SortPolicy sortPolicy) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
        this.sortPolicy = sortPolicy;
    }

    @Override
    public String name() {
        return "Closure of Scalar Optimization";
    }

    @Override
    public Term translate(TermTuple tuple, ExprUnary expr, TranslationContext context) {
        if (expr.op != ExprUnary.Op.CLOSURE && expr.op != ExprUnary.Op.RCLOSURE) return null;
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Closure argument must have arity 2");
        }

        AnnotatedTerm x = tuple.getAnnotatedTerm(0);
        AnnotatedTerm y = tuple.getAnnotatedTerm(1);
        Expr closedExpr = expr.sub;

        // cast x.e to scalar
        ExprVar probeAlloyVar = ExprVar.make(null, "%probe");
        AnnotatedVar probeVar = Term.mkVar("__@probe").of(x.getSort());
        context.addTermMapping(probeAlloyVar.label, new AnnotatedTerm(probeVar));
        Pair<AnnotatedTerm, AnnotatedTerm> scalarAndGuard;
        try {
            scalarAndGuard = scalarCaster.castToScalar(probeAlloyVar.join(closedExpr), context);
        } finally {
            context.removeMapping(probeAlloyVar.label);
        }
        if (scalarAndGuard == null) return null;  // x.e is not a scalar

        AnnotatedTerm scalar = scalarAndGuard.a;
        AnnotatedTerm guard = scalarAndGuard.b;

        if (!scalar.getFreeVars().contains(probeVar)
                && (guard == null || !guard.getFreeVars().contains(probeVar))) {
            // Neither contain the probe variable: value of scalar does not depend on x!
            // So [[(x,y) \in ^e]] := y = e
            return Term.mkEq(y.getTerm(), scalar.getTerm());
        }

        List<Term> scalarCalls = new ArrayList<>(); // scalarCalls[i] := y = f^{i+1}(x)
        List<Term> guardCalls = new ArrayList<>(); // guardCalls[i] := f^i(x) in dom(f)

        Sort tcSort = scalar.getSort(); // TODO verify this is the same as the input sort?
        int sortScope = sortPolicy.getSortScope(tcSort);
        context.markSortUnchanging(tcSort); // since we rely on the sort's scope here

        Term currentTerm = x.getTerm();
        for (int i = 0; i < sortScope; i++) {
            // guard: f^i(x) in dom(f)
            Term guardApp = (guard == null) ? Term.mkTop() : PortusUtil.substitute(
                    Collections.singletonList(probeVar), Collections.singletonList(currentTerm), guard.getTerm());
            // scalar: y = f^{i+1}(x)
            currentTerm = PortusUtil.substitute(
                    Collections.singletonList(probeVar), Collections.singletonList(currentTerm), scalar.getTerm());

            scalarCalls.add(Term.mkEq(y.getTerm(), currentTerm));
            guardCalls.add(guardApp);
        }

        // Assemble it
        Term assembled = Term.mkBottom();
        for (int i = sortScope - 1; i >= 0; i--) {
            assembled = Term.mkOr(scalarCalls.get(i), assembled); // y = f^{i+1}(x)
            // Add a guard for all the terms currently assembled
            assembled = Term.mkAnd(guardCalls.get(i), assembled); // f^i(x) in dom(f)
        }
        if (expr.op == ExprUnary.Op.RCLOSURE) {
            // add y = x for reflexive closure
            assembled = Term.mkOr(Term.mkEq(y.getTerm(), x.getTerm()), assembled);
        }

        // TODO make a definition for this!
        return assembled;
    }

}
