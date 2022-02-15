package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Top$;
import fortress.msfol.Var;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * The basic translator that provides unoptimized translations of every supported node.
 */
final class DefaultTranslator extends BaseTranslator {

    private final Map<Sig, Function<Var, Term>> sigMemberPredicates = new HashMap<>();
    private final Map<Sig, Sort> sigsToScopes = new HashMap<>();

    public DefaultTranslator(Translator topLevelTranslator) {
        super(topLevelTranslator);
    }

    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (sig instanceof Sig.PrimSig) {
            translatePrimSig((Sig.PrimSig) sig, context);
            // return Top because the returned Term doesn't matter for a Sig
            // this unfortunate syntax is the only way to access a Scala case object in Java
            return Top$.MODULE$;
        }
        return null;
    }

    private void translatePrimSig(Sig.PrimSig sig, TranslationContext context) {
        if (sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Internal error: seen sig " + sig.label + " before");
        }

        // Find the sort corresponding to this sig.
        Sort sort;
        if (sig.isTopLevel()) {
            // Top-level sig: make a new sort.
            sort = Sort.mkSortConst(makeUniqueName(sig.label));
            int scope = context.scoper.sig2scope(sig);
            context.addSort(sort, scope);
        } else {
            // Not top-level: its parent's sort should have been set before.
            sort = context.getSigSort(sig.parent);
            if (sort == null) {
                // It wasn't set: violation of the translate(Sig, TranslationContext) contract.
                throw new ErrorFatal("Sig " + sig.label + "'s parent had no SMT sort set.");
            }
        }
        context.setSigSort(sig, sort);

        // Make a new predicate for membership.
        String memPredName = makeUniqueName("in" + sig.label);
        sigMemberPredicates.put(sig, var -> Term.mkApp(memPredName, var));
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(memPredName, sort, Sort.Bool()));

        // Translate all its children so we can translate membership in them.
        for (Sig.PrimSig child : sig.children()) {
            recursivelyTranslate(child, context);
        }

        // Add axioms for membership
        for (Sig.PrimSig child : sig.children()) {
            context.addAxiom(makeSubsetAxiom(sig, child, context));
        }

        // Add axioms for disjointness between each pair of subsigs
        for (int i = 0; i < sig.children().size(); i++) {
            for (int j = i + 1; j < sig.children().size(); j++) {
                context.addAxiom(makeDisjointnessAxiom(
                        sig.children().get(i), sig.children().get(j), context));
            }
        }

        // Abstract sigs: add axiom that children cover sig
        if (sig.isAbstract != null) {
            context.addAxiom(makeCoverAxiom(sig, context));
        }
    }

    /** Create an axiom that child is a subset of parent. */
    private Term makeSubsetAxiom(Sig parent, Sig child, TranslationContext context) {
        // express in Alloy so we can translate to Fortress recursively
        // without assumptions on implementation of the translation
        // "all x: child | x in parent"
        Decl x = child.oneOf("x");
        Expr subsetAxiom = x.get().in(parent).forAll(x);
        return recursivelyTranslate(subsetAxiom, context);
    }

    /** Create an axiom that sig1 and sig2 are disjoint. */
    private Term makeDisjointnessAxiom(Sig sig1, Sig sig2, TranslationContext context) {
        // "all x1: child1, x2: child2 | not (x = y)
        Decl x1 = sig1.oneOf("x1");
        Decl x2 = sig2.oneOf("x2");
        Expr disjointnessAxiom = x1.get().equal(x2.get()).not().forAll(x1, x2);
        return recursivelyTranslate(disjointnessAxiom, context);
    }

    /** Create an axiom that parent's children cover all elements in the parent. */
    private Term makeCoverAxiom(Sig.PrimSig parent, TranslationContext context) {
        // "all x: sig | x in child1 or x in child2 or ... or x in childN
        Decl x = parent.oneOf("x");
        Expr disjunction = null;
        for (Sig.PrimSig child : parent.children()) {
            disjunction = x.get().in(child).or(disjunction);
        }
        if (disjunction == null) {
            // TODO: possible optimization: abstract sig with no children -> set scope to 0 regardless
            disjunction = ExprConstant.FALSE;
        }
        Expr completenessAxiom = disjunction.forAll(x);
        return recursivelyTranslate(completenessAxiom, context);
    }

}
