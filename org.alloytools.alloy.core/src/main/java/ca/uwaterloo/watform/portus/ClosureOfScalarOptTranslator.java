package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * An optimization for transitive closure over expressions that can be interpreted as Fortress functions.
 * If f: S->S is a function from scalars to scalars, then roughly we can translate:
 *   [[(x,y) \in ^f]] := y = f(x) || y = f(f(x)) || y = f(f(f(x))) || ... || y = f^{|S|}(x)
 * This is implemented as follows. If castToScalar(x.e) = (e(x), guard(x)) for a fresh variable x, then
 *   [[(x,y) \in ^e]] := guard(x) && (y = e(x) || (guard(e(x)) && (y = e(e(x))
 *       || (... guard(e^{|S|-1}(x)) && y = e^{|S|}(x)))))
 * We create a definition for the above and reuse it for closures over the same expression.
 *
 * Note that this is reliant upon x.f being a scalar - TODO recognize scalar-to-scalar functions.
 * A further possible optimization: if we know the maximum size of the range of the function and it's less than |S|,
 * we only have to go up to that size rather than |S|.
 */
final class ClosureOfScalarOptTranslator extends AbstractTranslator {

    // Cache for definitions created by this optimization.
    private final ExprCache<String> closureDefnNameCache;

    private final ScalarCaster scalarCaster;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public ClosureOfScalarOptTranslator(
            Translator topLevel, ScalarCaster scalarCaster, SortPolicy sortPolicy, NameGenerator nameGenerator) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.closureDefnNameCache = new ExprCache<>(sortPolicy);
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

        if (!x.getSort().equals(y.getSort())) return null; // let someone else deal with it

        // cast x.e to scalar
        ExprVar probeAlloyVar = ExprVar.make(null, "%probe");
        AnnotatedVar probeVar = Term.mkVar("__@probe").of(x.getSort());
        context.addTermMapping(probeAlloyVar.label, new AnnotatedTerm(probeVar));
        context.addFortressVar(probeVar);
        Pair<AnnotatedTerm, AnnotatedTerm> scalarAndGuard;
        try {
            scalarAndGuard = scalarCaster.castToScalar(probeAlloyVar.join(closedExpr), context);
        } finally {
            context.removeMapping(probeAlloyVar.label);
            context.removeFortressVar(probeVar);
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

        Sort tcSort = scalar.getSort();
        if (!tcSort.equals(x.getSort())) return null; // let someone else deal with it

        // Variables for the function definition
        AnnotatedVar xDefnVar = new AnnotatedVar(Term.mkVar(nameGenerator.freshName("x")), x.getSort());
        AnnotatedVar yDefnVar = new AnnotatedVar(Term.mkVar(nameGenerator.freshName("y")), y.getSort());

        Set<AnnotatedVar> freeVarSet = (guard == null) ? scalar.getFreeVars()
                : SetOps.union(scalar.getFreeVars(), guard.getFreeVars());
        List<AnnotatedVar> freeVars = freeVarSet.stream()
                .filter(aVar -> !aVar.equals(probeVar)) // remove the probe variable
                .sorted(Comparator.comparing(AnnotatedVar::name)) // sort alphabetically as arbitrary order
                .collect(Collectors.toList());

        List<AnnotatedVar> defnParams = SetOps.concatenate(Arrays.<AnnotatedVar>asList(xDefnVar, yDefnVar), freeVars);
        List<Term> defnArgs = SetOps.concatenate(
                Arrays.<Term>asList(x.getTerm(), y.getTerm()),
                (List<Term>) freeVars.stream()
                    .<Term>map(AnnotatedVar::variable)
                    .collect(Collectors.toList()));

        // See if we've cached it; include the closure/rclosure in the cache key to differentiate ^e and *e
        String cachedDefnName = closureDefnNameCache.get(expr, tcSort, context);
        if (cachedDefnName != null) {
            return Term.mkApp(cachedDefnName, defnArgs);
        }

        int sortScope = sortPolicy.getSortScope(tcSort);
        context.markSortUnchanging(tcSort); // since we rely on the sort's scope here

        List<Term> scalarCalls = new ArrayList<>(); // scalarCalls[i] := y = f^{i+1}(x)
        List<Term> guardCalls = new ArrayList<>(); // guardCalls[i] := f^i(x) in dom(f)

        Term currentTerm = xDefnVar.variable();
        for (int i = 0; i < sortScope; i++) {
            // guard: f^i(x) in dom(f)
            Term guardApp = (guard == null) ? Term.mkTop() : PortusUtil.substitute(
                    Collections.singletonList(probeVar), Collections.singletonList(currentTerm), guard.getTerm());
            // scalar: y = f^{i+1}(x)
            currentTerm = PortusUtil.substitute(
                    Collections.singletonList(probeVar), Collections.singletonList(currentTerm), scalar.getTerm());

            scalarCalls.add(Term.mkEq(yDefnVar.variable(), currentTerm));
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
            assembled = Term.mkOr(Term.mkEq(yDefnVar.variable(), xDefnVar.variable()), assembled);
        }

        // Make a definition and cache it for efficiency
        FunctionDefinition defn = new FunctionDefinition(
                nameGenerator.freshName("scalarTC"),
                CollectionConverters.asScala(defnParams).toSeq(),
                Sort.Bool(),
                assembled);
        context.addFunctionDefinition(defn);
        closureDefnNameCache.put(expr, tcSort, defn.name(), context);

        return Term.mkApp(defn.name(), defnArgs);
    }

}
