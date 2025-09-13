package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.List;
import java.util.stream.Collectors;

/**
 * A scheme for axioms to express relationships between signatures (and the field bounds).
 */
class SigAxioms {

    private final Translator rootTranslator;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public SigAxioms(Translator rootTranslator, SortPolicy sortPolicy, NameGenerator nameGenerator) {
        this.rootTranslator = rootTranslator;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
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

        AnnotatedVar x = Term.mkVar(nameGenerator.freshName("x")).of(sort);
        try {
            context.addFortressVar(x);
            Term inSig1 = rootTranslator.translate(ExprElementOf.make(x, sig1), context);
            Term inSig2 = rootTranslator.translate(ExprElementOf.make(x, sig2), context);
            return Term.mkForall(x, Term.mkNot(Term.mkAnd(inSig1, inSig2)));
        } finally {
            context.removeFortressVar(x);
        }
    }

    /**
     * Create an axiom asserting that a field's relation stays within its bound.
     */
    public Term makeFieldBoundConstraint(Sig.Field field, List<Sort> argSorts, TranslationContext context) {
        // We translate the bound for "sig A { f: M e }" as [[all this: A | this.f in M e]] to constrain the range,
        // plus a domain constraint: forall x1:S1,...,xn:Sn . [[(x1,...,xn) \in f]] => [[x1 \in A]].
        // This is how Kodkod does it (effectively), and it elegantly handles "this" (generated as a variable when
        // fields refer to previously declared fields) as well as multiplicities (handled by "in").
        // With the scalar optimizations on, this even works for functions optimized by the function optimization.
        // TODO: this can be optimized for one sigs.
        // The sig.decl field is "this: sig".
        Expr thisVar = field.sig.decl.get();
        Expr rangeAxiomAlloy = thisVar.join(field).in(field.decl().expr).forAll(field.sig.decl);
        Term rangeAxiom = rootTranslator.translate(rangeAxiomAlloy, context);

        List<AnnotatedVar> vars = argSorts.stream()
                .map(sort -> Term.mkVar(nameGenerator.freshName("x")).of(sort))
                .collect(Collectors.toList());
        Term domainAxiom;
        try {
            context.addFortressVars(vars);
            domainAxiom = Term.mkForall(vars, Term.mkImp(
                    rootTranslator.translate(ExprElementOf.make(TermTuple.fromVars(vars), field), context),
                    rootTranslator.translate(ExprElementOf.make(vars.get(0), field.sig), context)));
        } finally {
            context.removeFortressVars(vars);
        }

        return Term.mkAnd(domainAxiom, rangeAxiom);
    }

}
