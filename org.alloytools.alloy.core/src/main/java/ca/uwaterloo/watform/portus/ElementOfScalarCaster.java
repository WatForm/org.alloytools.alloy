package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import fortress.data.NameGenerator;
import fortress.msfol.AndList;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Eq;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import fortress.operations.TermOps;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A cast-to-scalar strategy that goes as follows: if [[x \in e]] translates to "guard && x = f" for some
 * Fortress expressions guard and f that don't depend on x, then f is a scalar representation of e with
 * the guard.
 *
 * The advantage of this is that it allows reusing logic from the translators for casting to scalar,
 * saving special cases: e.g. together with JoinOptTranslator and FunctionOptTranslator, this allows
 * casting "y.(x.f)" to "f(x,y)", where f is a binary function and x and y are variables.
 *
 * This has the effect of greatly increasing calls to the translators!
 */
final class ElementOfScalarCaster implements ScalarCaster {

    private final Translator rootTranslator;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;
    private final PortusStatistics statistics;

    // Unfortunately we have to keep state to avoid stack overflows: we shouldn't invoke this scalar caster
    // during the translations it invokes.
    // This means that this scalar caster is not threadsafe (but all of Portus likely isn't).
    private boolean currentlyRunning = false;

    public ElementOfScalarCaster(
            Translator rootTranslator, SortPolicy sortPolicy, NameGenerator nameGenerator, PortusStatistics statistics) {
        this.rootTranslator = rootTranslator;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.statistics = statistics;
    }

    @Override
    public String name() {
        return "Element-of";
    }

    @Override
    public Pair<AnnotatedTerm, AnnotatedTerm> castToScalar(Expr expr, TranslationContext context) {
        // Since we perform recursive translations, it's possible that this scalar caster gets
        // invoked during a translation it triggered. To avoid stack overflows, ignore any
        // such recursive calls.
        if (currentlyRunning) {
            return null;
        }
        currentlyRunning = true;

        Pair<AnnotatedTerm, AnnotatedTerm> result = castToScalarImpl(expr, context);

        currentlyRunning = false;
        return result;
    }

    private Pair<AnnotatedTerm, AnnotatedTerm> castToScalarImpl(Expr expr, TranslationContext context) {
        // Construct [[x \in expr]] for a fresh variable x.
        // First, find the sort of x.
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (resolvant.arity() != 1 || !resolvant.isDefinite()) {
            // Scalars have to have arity 1 and have definite sorts.
            // (Sort-circuiting on none is dealt with elsewhere.)
            return null;
        }
        Sort sort = resolvant.getDefiniteSorts().get(0);
        if (sort.equals(Sort.Bool())) {
            // Boolean expressions are formulas, not scalars.
            // Note: this should prune out a large number of large expressions that this function is
            // otherwise called on, because non-formula nodes tend to be close to the leaves of the AST.
            return null;
        }
        AnnotatedVar x = Term.mkVar(nameGenerator.freshName("x")).of(sort);

        // Translate [[x \in expr]] and see what we get.
        // Use a copy of the context to ignore side effects because this translation isn't being used.
        // FIXME: We can't currently copy the context because DefaultTranslator keeps the closure aux function state.
        // FIXME: Refactor by moving that state to TranslationContext, then we can copy the context here.
        // FIXME: Wait, but what if the result refers to a function that only makes sense in the mutated context?
        // TODO: Since we ignore side effects, cache entries from this translation are invalid because
        // TODO: further cache hits in the main translation will expect the side effect to have already occurred.
        Expr elementOf = ExprElementOf.make(x, expr);
//        TranslationContext contextCopy = new TranslationContext(context);
//        Term elementOfResult = rootTranslator.translate(elementOf, contextCopy);
        Term elementOfResult;
        try {
            context.addFortressVar(x);
            elementOfResult = rootTranslator.translate(elementOf, context);
        } finally {
            context.removeFortressVar(x);
        }

        // See if it's of the form "guard && x = f".
        // There should be one conjunct of the form "x = f", and the rest shouldn't reference x (they're the guard).
        List<Term> conjuncts = collectConjuncts(elementOfResult);
        List<Term> guardConjuncts = new ArrayList<>();
        Term scalar = null;
        for (Term conjunct : conjuncts) {
            if (isVarFreeInTerm(x.variable(), conjunct)) {
                // Should be the scalar - must be of the form "x = scalar" or "scalar = x"
                if (scalar != null) {
                    // multiple of them: not of the correct form
                    return null;
                }
                if (!(conjunct instanceof Eq)) {
                    // not of the correct form
                    return null;
                }

                Eq eq = (Eq) conjunct;
                if (eq.left().equals(x.variable())) {
                    scalar = eq.right();
                } else if (eq.right().equals(x.variable())) {
                    scalar = eq.left();
                } else {
                    // neither are x - not of the correct form
                    return null;
                }

                // The scalar term shouldn't reference x
                if (isVarFreeInTerm(x.variable(), scalar)) {
                    return null;
                }
            } else {
                // Part of the guard
                guardConjuncts.add(conjunct);
            }
        }

        if (scalar == null) {
            // Didn't successfully find a "x = scalar" term
            return null;
        }

        // Success! Format into a guard and scalar.
        Term guard;
        if (guardConjuncts.isEmpty()) {
            guard = Term.mkTop();
        } else {
            guard = Term.mkAnd(guardConjuncts);
        }

        // TODO: what about free variables? We can't determine their sorts
        // For now, destroy the effectiveness of this optimization by not handling the case where
        // there are any free variables in the scalar. In the future maybe every translator should
        // return an AnnotatedTerm.
        // Also TODO: should we be using getTheory()?
        if (!TermOps.wrapTerm(scalar).freeVars(context.getTheory().signature()).isEmpty()) {
            statistics.elementOfScalarCasterIgnoredDueToFreeVarsCount.increment();
            return null;
        }

        return new Pair<>(new AnnotatedTerm(scalar, sort), new AnnotatedTerm(guard, Sort.Bool()));
    }

    private List<Term> collectConjuncts(Term term) {
        if (term instanceof AndList) {
            AndList and = (AndList) term;
            return CollectionConverters.asJava(and.arguments()).stream()
                    .map(this::collectConjuncts)
                    .reduce(new ArrayList<>(), SetOps::concatenate);
        } else {
            return Collections.singletonList(term);
        }
    }

    private boolean isVarFreeInTerm(Var var, Term term) {
        return TermOps.wrapTerm(term).freeVarConstSymbols().contains(var);
    }

}
