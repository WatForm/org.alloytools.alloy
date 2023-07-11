package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.Collections;
import java.util.List;

/**
 * A scheme for axioms to express the relationships between signatures.
 */
class SigAxioms {

    private final Translator rootTranslator;
    private final SortPolicy sortPolicy;

    public SigAxioms(Translator rootTranslator, SortPolicy sortPolicy) {
        this.rootTranslator = rootTranslator;
        this.sortPolicy = sortPolicy;
    }

    /**
     * Generate all the axioms needed to completely specify the relations between a PrimSig
     * and its children.
     */
    public final void addPrimSigChildrenAxioms(Sig.PrimSig sig, TranslationContext context) {
        // Add axioms for membership
        for (Sig.PrimSig child : sig.children()) {
            context.addAxiom(makeSubsetAxiom(Collections.singletonList(sig), child, context));
        }

        // Add axioms for disjointness between each pair of subsigs
        assertSigsPairwiseDisjoint(sig.children().makeConstList(), context);

        // Abstract sigs: add axiom that children cover sig
        // Note: abstracts sig without children aren't treated as abstract
        // (see, for example, Kodkod's output given "abstract sig A {}; run {}")
        if (sig.isAbstract != null && !sig.children().isEmpty()) {
            context.addAxiom(makeCoverAxiom(sig, context));
        }
    }

    /** Create an axiom that child is a subset of the union of parents. If exact, declare it equal instead. */
    public Term makeSubsetAxiom(List<Sig> parents, Expr child, boolean exact, TranslationContext context) {
        // express in Alloy so we can translate to Fortress recursively
        // without assumptions on implementation of the translation
        // Alloy: "child in parent1 + parent2 + ... + parentn", no need to overcomplicate things
        // If exact, instead "child = parent1 + parent2 + ... + parentn"
        Expr union = parents.stream()
                .map(sig -> (Expr) sig) // annoying casting step necessary to satisfy the whims of Java generics
                .reduce(Expr::plus)
                .orElseThrow(() -> new ErrorFatal("Internal Portus error: subset axiom with no parents!"));
        Expr subsetAxiom = exact ? child.equal(union) : child.in(union);
        return rootTranslator.translate(subsetAxiom, context);
    }

    /** Default for convenience: not exact. */
    public final Term makeSubsetAxiom(List<Sig> parents, Expr child, TranslationContext context) {
        return makeSubsetAxiom(parents, child, false, context);
    }

    /** Add axioms to context that assert that all the sigs are pairwise disjoint. */
    public void assertSigsPairwiseDisjoint(List<? extends Sig> sigs, TranslationContext context) {
        for (int i = 0; i < sigs.size(); i++) {
            for (int j = i + 1; j < sigs.size(); j++) {
                context.addAxiom(makeSigsDisjointAxiom(sigs.get(i), sigs.get(j), context));
            }
        }
    }

    /** Create an axiom that the two sigs are disjoint. */
    public Term makeSigsDisjointAxiom(Sig sig1, Sig sig2, TranslationContext context) {
        // "forall x: S | !([[x \in sig1]] && [[x \in sig2]])
        Sort sort = sortPolicy.getSort(sig1);
        if (sort == null || !sort.equals(sortPolicy.getSort(sig2))) {
            // short-circuit: they must be disjoint since they're in different sorts
            return Term.mkTop();
        }

        AnnotatedVar x = Term.mkVar(context.nameGenerator.freshName("x")).of(sort);
        Term inSig1 = rootTranslator.translate(ExprElementOf.make(x, sig1), context);
        Term inSig2 = rootTranslator.translate(ExprElementOf.make(x, sig2), context);
        return Term.mkForall(x, Term.mkNot(Term.mkAnd(inSig1, inSig2)));
    }

    /** Create an axiom that parent's children cover all elements in the parent. */
    public Term makeCoverAxiom(Sig.PrimSig parent, TranslationContext context) {
        // Alloy: "all x: sig | x in child1 or x in child2 or ... or x in childN" (KT 4.2)
        Decl x = parent.oneOf("x");
        Expr disjunction = null;
        for (Sig.PrimSig child : parent.children()) {
            disjunction = x.get().in(child).or(disjunction);
        }
        if (disjunction == null) {
            disjunction = ExprConstant.FALSE;
        }
        Expr completenessAxiom = disjunction.forAll(x);
        return rootTranslator.translate(completenessAxiom, context);
    }

}
