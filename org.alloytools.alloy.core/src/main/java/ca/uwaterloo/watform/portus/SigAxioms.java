package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

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
     * Generate the axioms needed to naively handle one, lone, and some sigs.
     */
    public void addSigMultiplicityAxiom(Sig sig, TranslationContext context) {
        Expr axiom;
        if (sig.isOne != null) {
            axiom = sig.one();
        } else if (sig.isLone != null) {
            axiom = sig.lone();
        } else if (sig.isSome != null) {
            axiom = sig.some();
        } else {
            return;
        }
        context.addAxiom(rootTranslator.translate(axiom, context));
    }

    /**
     * Generate all the axioms needed to completely specify the relations between a PrimSig
     * and its children.
     */
    public void addPrimSigChildrenAxioms(Sig.PrimSig sig, TranslationContext context) {
        // Add the axiom for the relationship between parents and children.
        context.addAxiom(makeParentChildAxiom(sig, context));

        // Add axioms for disjointness between each pair of subsigs
        assertSigsPairwiseDisjoint(sig.children().makeConstList(), context);
    }

    /**
     * Create the axiom governing the relationship between parent and its children.
     * If parent is not abstract, the axiom states the children are a subset of the parent.
     * If parent is abstract, the axiom states the union of the children equal the parent.
     */
    public Term makeParentChildAxiom(Sig.PrimSig parent, TranslationContext context) {
        // Alloy: "child1 + child2 + ... + childN in parent" if non-abstract,
        // "child1 + child2 + ... + childN = parent" if abstract.

        // Note that even abstract sigs without children aren't treated as abstract
        // (see, for example, Kodkod's output given "abstract sig A {}; run {}")
        // so we can completely ignore this axiom if there are no children
        // (rather than generating "none in parent" / "none = parent" like if the union was followed strictly).
        if (parent.children().isEmpty()) {
            return Term.mkTop();
        }

        //noinspection OptionalGetWithoutIsPresent
        Expr union = parent.children().makeConstList().stream()
                .map(sig -> (Expr) sig)
                .reduce(Expr::plus)
                .get();
        Expr axiom = (parent.isAbstract != null) ? union.equal(parent) : union.in(parent);
        return rootTranslator.translate(axiom, context);
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

}
