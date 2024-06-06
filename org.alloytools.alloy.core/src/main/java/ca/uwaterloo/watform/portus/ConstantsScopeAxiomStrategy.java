package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Sig;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * A scope axiom strategy using the following axioms: suppose sig is part of sort S with scope n.
 * Then "sig has scope at most k" is equivalent to "there exist n-k distinct constants in S which are not in sig".
 * For an exact scope of k, we also assert the existance of k distinct constants which *are* in sig.
 */
final class ConstantsScopeAxiomStrategy implements ScopeAxiomStrategy {

    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public ConstantsScopeAxiomStrategy(SortPolicy sortPolicy, NameGenerator nameGenerator) {
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public Term makeNonExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        Sort sort = sortPolicy.getSort(sig);
        if (sort == null) {
            throw new ErrorFatal("Can only generate a constants scope axiom for sigs with defined sorts!");
        }
        int sortScope = sortPolicy.getSortScope(sort);

        // Generate sortScope - scope constants and assert that they are distinct and not in sig
        Function<AnnotatedVar, Term> notInSig = var ->
                recursiveTranslator.translate(ExprElementOf.make(var, sig).not(), context);
        return generateDistinctConstantsAxiom(sortScope - scope, sort, notInSig, context);
    }

    @Override
    public Term makeExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        Sort sort = sortPolicy.getSort(sig);
        if (sort == null) {
            throw new ErrorFatal("Can only generate a constants scope axiom for sigs with defined sorts!");
        }

        // Add on to the non-exact scope axiom that there are also scope constants which are distinct and in sig
        Term scopeAtMost = makeNonExactScopeAxiom(sig, scope, recursiveTranslator, context);

        // This actually asserts that the scope is at least `scope`, so the conjunction gives equality
        Function<AnnotatedVar, Term> inSig = var ->
                recursiveTranslator.translate(ExprElementOf.make(var, sig), context);
        Term scopeAtLeast = generateDistinctConstantsAxiom(scope, sort, inSig, context);
        return Term.mkAnd(scopeAtMost, scopeAtLeast);
    }

    /**
     * Generate numConstants distinct constants of sort and add them to the context.
     * Return a term asserting that they're all distinct and assertion(c) holds for each constant c.
     */
    private Term generateDistinctConstantsAxiom(
            int numConstants, Sort sort, Function<AnnotatedVar, Term> assertion, TranslationContext context) {
        List<Term> constants = new ArrayList<>();
        List<Term> assertions = new ArrayList<>();

        // Generate all constants and their assertions
        for (int i = 0; i < numConstants; i++) {
            String name = nameGenerator.freshName("scope_" + sort.name() + "_" + i);
            Var constant = Term.mkVar(name);
            constants.add(constant);

            context.addConstant(constant.of(sort));
            assertions.add(assertion.apply(constant.of(sort)));
        }

        // Also assert they're distinct if there's at least 2 of them - mkDistinct fails for 0 or 1 arguments
        if (constants.size() >= 2) {
            assertions.add(Term.mkDistinct(constants));
        }

        // If we didn't happen to generate anything (say 0 constants were requested), just return Top
        if (assertions.isEmpty()) {
            return Term.mkTop();
        }
        return Term.mkAnd(assertions);
    }

}
