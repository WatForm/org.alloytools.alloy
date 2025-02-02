package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import scala.collection.immutable.Seq;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * An optimization for transitive closure over expressions that can be interpreted as Fortress functions.
 * If f: S->S is a function from scalars to scalars, then roughly we can translate:
 *   [[(x,y) \in ^f]] := y = f(x) || y = f(f(x)) || y = f(f(f(x))) || ... || y = f^{|S|}(x)
 * This is implemented as follows. If castToScalar(e) = (e(x), guard(x)) for a fresh variable x, then
 *   [[(x,y) \in ^e]] := guard(x) && (y = e(x) || (guard(e(x)) && (y = e(e(x))
 *       || (... guard(e^{|S|-1}(x)) && y = e^{|S|}(x)))))
 * We create a definition for the above and reuse it for closures over the same expression.
 *
 * A further possible optimization: if we know the maximum size of the range of the function and it's less than |S|,
 * we only have to go up to that size rather than |S|.
 */
final class ClosureOfScalarOptTranslator extends AbstractTranslator {

    // Cache for definitions created by this optimization.
    private final ExprCache<String> closureDefnNameCache;

    // Cache for definitions of nested functions: the ith defn is 2^i applications of the function.
    private final ExprCache<Pair<List<String>, List<Term>>> nestedScalarDefnNameCache;

    private final ScalarCaster scalarCaster;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    private final boolean useSquareDefns;

    public ClosureOfScalarOptTranslator(
            Translator topLevel, ScalarCaster scalarCaster, SortPolicy sortPolicy, NameGenerator nameGenerator,
            boolean useSquareDefns) {
        super(topLevel);
        this.scalarCaster = scalarCaster;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.useSquareDefns = useSquareDefns;
        this.closureDefnNameCache = new ExprCache<>(sortPolicy);
        this.nestedScalarDefnNameCache = new ExprCache<>(sortPolicy);
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

        // If the sorts don't work out, let someone else deal with it
        if (!x.getSort().equals(y.getSort())) {
            return null;
        }

        Scalar closedScalar = scalarCaster.castToScalar(expr.sub, context);
        if (closedScalar == null || closedScalar.getArity() != 1 || !y.getSort().equals(closedScalar.getResultSort())) {
            // arity != 1 should be impossible, but let someone else deal with it otherwise
            return null;
        }

        Sort tcSort = closedScalar.getResultSort();
        int sortScope = sortPolicy.getSortScope(tcSort);
        context.markSortUnchanging(tcSort); // since we rely on the sort's scope here

        // Variables for the function definition
        AnnotatedVar xDefnVar = new AnnotatedVar(Term.mkVar(nameGenerator.freshName("x")), x.getSort());
        AnnotatedVar yDefnVar = new AnnotatedVar(Term.mkVar(nameGenerator.freshName("y")), y.getSort());

        boolean reflexive = (expr.op == ExprUnary.Op.RCLOSURE);
        Term defnBody;
        try {
            context.addFortressVars(xDefnVar, yDefnVar);
            defnBody = buildClosureTerm(
                    expr.sub, new AnnotatedTerm(xDefnVar), yDefnVar.variable(), closedScalar, sortScope, reflexive,
                    context);
        } finally {
            context.removeFortressVars(xDefnVar, yDefnVar);
        }

        List<AnnotatedVar> freeVars = PortusUtil.computeFreeVariables(expr, context, sortPolicy);
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

        // Make a definition and cache it for efficiency
        FunctionDefinition defn = new FunctionDefinition(
                nameGenerator.freshName("scalarTC"),
                CollectionConverters.asScala(defnParams).toSeq(),
                Sort.Bool(),
                defnBody);
        context.addFunctionDefinition(defn);
        closureDefnNameCache.put(expr, tcSort, defn.name(), context);

        return Term.mkApp(defn.name(), defnArgs);
    }

    private Term buildClosureTerm(
            Expr cacheKey, AnnotatedTerm x, Term y, Scalar scalar, int sortScope, boolean reflexive,
            TranslationContext context) {
        Term assembled = Term.mkBottom();
        for (int i = sortScope - 1; i >= 0; i--) {
            // y = f^{i+1}(x)
            Term iPlus1Nested = buildNestedCall(cacheKey, scalar, x, i + 1, context).getTerm();
            assembled = Term.mkOr(Term.mkEq(y, iPlus1Nested), assembled);

            // guard(f^i(x))
            AnnotatedTerm iNested = buildNestedCall(cacheKey, scalar, x, i, context);
            assembled = Term.mkAnd(scalar.getGuard(new TermTuple(iNested), context), assembled);
        }

        if (reflexive) {
            // add y = x for reflexive closure
            assembled = Term.mkOr(Term.mkEq(y, x.getTerm()), assembled);
        }

        return assembled;
    }

    // note: cache key should NOT include ^/* because it can be shared
    private AnnotatedTerm buildNestedCall(
            Expr cacheKey, Scalar scalar, AnnotatedTerm arg, int numNestings, TranslationContext context) {
        if (useSquareDefns) {
            return buildSquareDefnsNestedCall(cacheKey, scalar, arg, numNestings, context);
        } else {
            return buildPlainNestedCall(scalar, arg, numNestings, context);
        }
    }

    private AnnotatedTerm buildPlainNestedCall(
            Scalar scalar, AnnotatedTerm arg, int numNestings, TranslationContext context) {
        AnnotatedTerm result = arg;
        for (int i = 0; i < numNestings; i++) {
            result = scalar.getAnnotatedScalar(new TermTuple(result), context);
        }
        return result;
    }

    private AnnotatedTerm buildSquareDefnsNestedCall(
            Expr cacheKey, Scalar scalar, AnnotatedTerm arg, int numNestings, TranslationContext context) {
        Pair<List<String>, List<Term>> squareDefnsAndFreeVars = nestedScalarDefnNameCache.get(
                cacheKey, scalar.getResultSort(), context);
        if (squareDefnsAndFreeVars == null) {
            squareDefnsAndFreeVars = makeSquareDefns(scalar, context);
            nestedScalarDefnNameCache.put(cacheKey, scalar.getResultSort(), squareDefnsAndFreeVars, context);
        }
        List<String> squareDefns = squareDefnsAndFreeVars.a;
        List<Term> freeVars = squareDefnsAndFreeVars.b;

        // Express numNestings in binary and apply each definition accordingly
        Term result = arg.getTerm();
        for (int i = 0; i < squareDefns.size(); i++) {
            if ((numNestings & (1 << i)) != 0) {
                // numNestings has a 1 in this index in binary: apply the term
                result = Term.mkApp(squareDefns.get(i), SetOps.concatenate(result, freeVars));
            }
        }
        return new AnnotatedTerm(result, scalar.getResultSort());
    }

    // Make definitions expressing f, f^2, f^4, f^8, ..., f^|sort|
    // Second element is the list of free variables to pass
    private Pair<List<String>, List<Term>> makeSquareDefns(Scalar scalar, TranslationContext context) {
        int sortSize = sortPolicy.getSortScope(scalar.getResultSort());
        List<String> defns = new ArrayList<>();
        AnnotatedVar param = Term.mkVar(nameGenerator.freshName("x")).of(scalar.getArgSorts().get(0));

        Term scalarBody;
        List<AnnotatedVar> freeAnnVars;
        try {
            context.addFortressVar(param);
            scalarBody = scalar.getScalar(TermTuple.fromVars(param), context);
            freeAnnVars = PortusUtil.computeTermFreeVars(scalarBody, context).stream()
                    .filter(avar -> !avar.equals(param)) // remove the param - we only want extra free vars
                    .collect(Collectors.toList());
        } finally {
            context.removeFortressVar(param);
        }
        List<Term> freeVars = freeAnnVars.stream().map(AnnotatedVar::variable).collect(Collectors.toList());

        Seq<AnnotatedVar> paramList = CollectionConverters.asScala(SetOps.concatenate(param, freeAnnVars)).toSeq();

        String lastDefn = null;
        for (int i = 1; i <= sortSize; i *= 2) {
            Term body;
            if (i == 1) {
                body = scalarBody;
            } else {
                Term innerCall = Term.mkApp(lastDefn, SetOps.concatenate(param.variable(), freeVars));
                body = Term.mkApp(lastDefn, SetOps.concatenate(innerCall, freeVars));
            }

            String defnName = nameGenerator.freshName("closureNest" + i);
            FunctionDefinition defn = new FunctionDefinition(defnName, paramList, scalar.getResultSort(), body);
            context.addFunctionDefinition(defn);

            defns.add(defnName);
            lastDefn = defnName;
        }

        return new Pair<>(defns, freeVars);
    }

}
