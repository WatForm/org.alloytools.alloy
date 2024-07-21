package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Sig;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A scope axiom strategy which uses nested quantifiers to express the axioms.
 */
final class QuantifierScopeAxiomStrategy implements ScopeAxiomStrategy {

    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public QuantifierScopeAxiomStrategy(SortPolicy sortPolicy, NameGenerator nameGenerator) {
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
    }

    @Override
    public Term makeExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        // Fortress: "exists x1, ..., xn: sort . forall x: sort . !(x1 = x2) && ...
        // && !(x1 = xn) && !(x2 = x3) && ... && !(x{n-1} = xn) && ([[x \in sig]] <=> x = x1
        // || ... || x = xn)" (KT 4.3)
        List<AnnotatedVar> vars = makeVars(scope, sig);
        AnnotatedVar x = AnnotatedVar.apply(Term.mkVar(nameGenerator.freshName("x")), sortPolicy.getSort(sig));

        try {
            context.addFortressVars(vars);
            context.addFortressVar(x);

            // construct the !(xi = xj) conjuncts
            List<Term> conjuncts = new ArrayList<>();
            for (int i = 0; i < scope; i++) {
                for (int j = i + 1; j < scope; j++) {
                    conjuncts.add(Term.mkNot(Term.mkEq(vars.get(i).variable(), vars.get(j).variable())));
                }
            }

            // construct the x = xi disjuncts
            List<Term> eqDisjuncts = vars.stream()
                    .map(var -> Term.mkEq(x.variable(), var.variable()))
                    .collect(Collectors.toList());

            // construct the last conjunct
            Term xInChild = recursiveTranslator.translate(ExprElementOf.make(x, sig), context);
            Term implication = Term.mkIff(xInChild, Term.mkOr(eqDisjuncts));
            conjuncts.add(implication);

            // construct the final axiom
            return Term.mkExists(vars, Term.mkForall(x, Term.mkAnd(conjuncts)));
        } finally {
            context.removeFortressVar(x);
            context.removeFortressVars(vars);
        }
    }

    @Override
    public Term makeNonExactScopeAxiom(Sig sig, int scope, Translator recursiveTranslator, TranslationContext context) {
        // Fortress: "forall x1, ..., x{n+1}: sort . [[x1 \in child]] && ... && [[x{n+1} \in child]] =>
        // x1 = x2 || .. || x1 = x{n+1} || x2 = x3 || ... || xn = x{n+1}" (KT 4.3)
        int numVars = scope + 1;
        List<AnnotatedVar> vars = makeVars(numVars, sig);

        try {
            context.addFortressVars(vars);

            // construct the conjuncts
            List<Term> conjuncts = vars.stream()
                    .map(var -> recursiveTranslator.translate(ExprElementOf.make(var, sig), context))
                    .collect(Collectors.toList());
            Term conjunction = Term.mkAnd(conjuncts);

            // construct the O(scope^2) disjuncts
            List<Term> disjuncts = new ArrayList<>();
            for (int i = 0; i < numVars; i++) {
                for (int j = i + 1; j < numVars; j++) {
                    disjuncts.add(Term.mkEq(vars.get(i).variable(), vars.get(j).variable()));
                }
            }
            Term disjunction = Term.mkOr(disjuncts);

            // construct the forall and the final axiom
            return Term.mkForall(vars, Term.mkImp(conjunction, disjunction));
        } finally {
            context.removeFortressVars(vars);
        }
    }

    private List<AnnotatedVar> makeVars(int numVars, Sig sig) {
        List<AnnotatedVar> vars = new ArrayList<>(numVars);
        Sort sigSort = sortPolicy.getSort(sig);
        assert sigSort != null;
        for (int i = 0; i < numVars; i++) {
            vars.add(AnnotatedVar.apply(Term.mkVar(nameGenerator.freshName("x" + i)), sigSort));
        }
        return vars;
    }

}
