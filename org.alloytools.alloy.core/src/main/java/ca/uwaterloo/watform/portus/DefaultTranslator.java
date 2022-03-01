package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Top$;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * The basic translator that provides unoptimized translations of every supported node.
 */
final class DefaultTranslator extends AbstractTranslator {

    // Membership predicates for each signature (see KT 4.2).
    private final Map<Sig, Function<Var, Term>> sigMemberPredicates = new HashMap<>();

    public DefaultTranslator(Translator topLevelTranslator) {
        super(topLevelTranslator);
    }

    /** Translate a PrimSig declaration. */
    @Override
    public Term translate(Sig.PrimSig sig, TranslationContext context) {
        if (sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Internal error: seen sig " + sig.label + " before");
        }

        // Find the sort corresponding to this sig.
        Sort sort;
        if (sig.isTopLevel()) {
            // Top-level sig: make a new sort.
            sort = Sort.mkSortConst(uniqueNameGenerator.make(sig.label));
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
        String memPredName = uniqueNameGenerator.make("in" + sig.label);
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

        // Subsigs: generate scope constraints
        if (!sig.isTopLevel()) {
            int scope = context.scoper.sig2scope(sig);
            if (context.scoper.isExact(sig)) {
                context.addAxiom(makeExactSubsigScopeAxiom(sig, sort, scope, context));
            } else {
                context.addAxiom(makeNonExactSubsigScopeAxiom(sig, sort, scope, context));
            }
        }

        // return Top because the returned Term doesn't matter for a Sig
        // this unfortunate syntax is the only way to access a Scala case object in Java
        return Top$.MODULE$;
    }

    /** Create an axiom that child is a subset of parent. */
    private Term makeSubsetAxiom(Sig parent, Sig child, TranslationContext context) {
        // express in Alloy so we can translate to Fortress recursively
        // without assumptions on implementation of the translation
        // Alloy: "all x: child | x in parent" (KT 4.2)
        Decl x = child.oneOf("x");
        Expr subsetAxiom = x.get().in(parent).forAll(x);
        return recursivelyTranslate(subsetAxiom, context);
    }

    /** Create an axiom that sig1 and sig2 are disjoint. */
    private Term makeDisjointnessAxiom(Sig sig1, Sig sig2, TranslationContext context) {
        // Alloy: "all x1: child1, x2: child2 | not (x = y)" (KT 4.2)
        Decl x1 = sig1.oneOf("x1");
        Decl x2 = sig2.oneOf("x2");
        Expr disjointnessAxiom = x1.get().equal(x2.get()).not().forAll(x1, x2);
        return recursivelyTranslate(disjointnessAxiom, context);
    }

    /** Create an axiom that parent's children cover all elements in the parent. */
    private Term makeCoverAxiom(Sig.PrimSig parent, TranslationContext context) {
        // Alloy: "all x: sig | x in child1 or x in child2 or ... or x in childN" (KT 4.2)
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

    /** Create an axiom that the child subsig has an exact scope of `scope`. */
    private Term makeExactSubsigScopeAxiom(Sig child, Sort sort, int scope, TranslationContext context) {
        // Fortress: "exists x1, ..., xn: sort . forall x: sort . !(x1 = x2) && ...
        // && !(x1 = xn) && !(x2 = x3) && ... && !(x{n-1} = xn) && ([[x \in child]] <=> x = x1
        // || ... || x = xn)" (KT 4.3)
        Var[] vars = new Var[scope];
        for (int i = 0; i < vars.length; i++) {
            vars[i] = Term.mkVar("x" + i);
        }
        Var x = Term.mkVar("x");

        // construct the !(xi = xj) conjuncts
        List<Term> conjuncts = new ArrayList<>();
        for (int i = 0; i < vars.length; i++) {
            for (int j = i+1; j < vars.length; j++) {
                conjuncts.add(Term.mkNot(Term.mkEq(vars[i], vars[j])));
            }
        }

        // construct the x = xi disjuncts
        List<Term> eqDisjuncts = Arrays.stream(vars)
                .map(var -> Term.mkEq(x, var))
                .collect(Collectors.toList());

        // construct the last conjunct
        Term xInChild = recursivelyTranslate(ExprElementOf.make(x, child), context);
        Term implication = Term.mkIff(xInChild, Term.mkOr(eqDisjuncts));
        conjuncts.add(implication);

        // construct the decls
        List<AnnotatedVar> varDecls = Arrays.stream(vars)
                .map(var -> var.of(sort))
                .collect(Collectors.toList());

        // construct the final axiom
        return Term.mkExists(varDecls, Term.mkForall(x.of(sort), Term.mkAnd(conjuncts)));
    }

    /** Create an axiom that the child subsig has a non-exact scope of `scope`. */
    private Term makeNonExactSubsigScopeAxiom(Sig child, Sort sort, int scope, TranslationContext context) {
        // Fortress: "forall x1, ..., x{n+1}: sort . [[x1 \in child]] && ... && [[x{n+1} \in child]] =>
        // x1 = x2 || .. || x1 = x{n+1} || x2 = x3 || ... || xn = x{n+1}" (KT 4.3)
        Var[] vars = new Var[scope + 1];
        for (int i = 0; i < vars.length; i++) {
            vars[i] = Term.mkVar("x" + i);
        }

        // construct the conjuncts
        List<Term> conjuncts = Arrays.stream(vars)
                .map(var -> recursivelyTranslate(ExprElementOf.make(var, child), context))
                .collect(Collectors.toList());
        Term conjunction = Term.mkAnd(conjuncts);

        // construct the O(scope^2) disjuncts
        List<Term> disjuncts = new ArrayList<>();
        for (int i = 0; i < vars.length; i++) {
            for (int j = i+1; j < vars.length; j++) {
                disjuncts.add(Term.mkEq(vars[i], vars[j]));
            }
        }
        Term disjunction = Term.mkOr(disjuncts);

        // construct the forall and the final axiom
        List<AnnotatedVar> decls = Arrays.stream(vars)
                .map(var -> var.of(sort))
                .collect(Collectors.toList());
        return Term.mkForall(decls, Term.mkImp(conjunction, disjunction));
    }

    /** Translate "tuple \in expr", where expr is an ExprBinary term. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprBinary expr, TranslationContext context) {
        switch (expr.op) {
            // see KT figure 4.10
            case PLUS: // union
                return Term.mkOr(
                        recursivelyTranslate(ExprElementOf.make(tuple, expr.left), context),
                        recursivelyTranslate(ExprElementOf.make(tuple, expr.right), context));
            case INTERSECT:
                return Term.mkAnd(
                        recursivelyTranslate(ExprElementOf.make(tuple, expr.left), context),
                        recursivelyTranslate(ExprElementOf.make(tuple, expr.right), context));
            case MINUS: // set difference
                return Term.mkAnd(
                        recursivelyTranslate(ExprElementOf.make(tuple, expr.left), context),
                        Term.mkNot(
                                recursivelyTranslate(ExprElementOf.make(tuple, expr.right), context)));
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprBinary term: " + expr.op);
        }
    }

    /** Translate an ExprBinary formula. */
    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        switch (expr.op) {
            // see KT figure 4.6
            case IMPLIES:
                return Term.mkImp(
                        recursivelyTranslate(expr.left, context),
                        recursivelyTranslate(expr.right, context));
            case IFF:
                return Term.mkIff(
                        recursivelyTranslate(expr.left, context),
                        recursivelyTranslate(expr.right, context));
            case AND:
            case OR:
                // confusingly, AND and OR aren't real ExprBinary ops
                throw new ErrorFatal("AND and OR should be ExprLists!");
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprBinary formula: " + expr.op);
        }
    }

    /** Translate an ExprUnary formula. */
    @Override
    public Term translate(ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOT:
                // see KT figure 4.6
                return Term.mkNot(
                        recursivelyTranslate(expr.sub, context));
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprUnary formula: " + expr.op);
        }
    }

    /** Translate an ExprList formula. */
    @Override
    public Term translate(ExprList expr, TranslationContext context) {
        // first, just translate all the args
        List<Term> translatedArgs = expr.args.stream()
                .map(arg -> recursivelyTranslate(arg, context))
                .collect(Collectors.toList());

        switch (expr.op) {
            // see KT figure 4.6, extended to any number of ops
            case AND:
                return Term.mkAnd(translatedArgs);
            case OR:
                return Term.mkOr(translatedArgs);
            default:
                // we don't yet support DISJOINT or TOTALORDER
                throw new ErrorFatal("Unsupported ExprList formula: " + expr.op);
        }
    }

    /** Translate an ExprQt formula. */
    // TODO: COMPREHENSION is a term not a formula, so is SUM
    @Override
    public Term translate(ExprQt expr, TranslationContext context) {
        // "no x: e | f" gets translated to "all x: e | not f"
        if (expr.op == ExprQt.Op.NO) {
            // unfortunately forAll()'s API doesn't support taking just a list of decls
            Expr translation = ExprQt.Op.ALL.make(null, null, expr.decls, expr.sub.not());
            return recursivelyTranslate(translation, context);
        }

        // Deal with disjoint by desugaring
        Expr desugared = expr.desugar();
        if (desugared instanceof ExprQt) {
            // we can continue to translate it here
            expr = (ExprQt) desugared;
        } else {
            return recursivelyTranslate(desugared, context);
        }

        // Translate all the decls into Fortress
        Pair<List<AnnotatedVar>, Term> varsAndCond = translateDeclList(expr.decls, context);
        List<AnnotatedVar> vars = varsAndCond.a;
        Term condition = varsAndCond.b;

        // Process the formula itself - see KT figure 4.6
        Term sub = recursivelyTranslate(expr.sub, context);
        switch (expr.op) {
            case ALL:
                // forall x1: S1, ..., xn: Sn . [[x1 \in e1]] && ... && [[xn \in en]] => [[sub]]
                return Term.mkForall(vars, Term.mkImp(condition, sub));
            case SOME:
                // exists x1: S1, ..., xn: Sn . [[x1 \in e1]] && ... && [[xn \in en]] && [[sub]]
                return Term.mkExists(vars, Term.mkAnd(condition, sub));
            case LONE: {
                // naive for now
                // forall x, y: S . [[x \in e]] && [[y \in e]] && [[f]] && [[f[x/y]]] => x = y
                List<AnnotatedVar> primed = prime(vars);
                Term primedCondition = PortusUtil.substitute(vars, primed, condition);
                Term primedSub = PortusUtil.substitute(vars, primed, sub);
                Term equal = PortusUtil.mkVarsEqual(vars, primed);
                return Term.mkForall(vars, Term.mkForall(primed, Term.mkImp(
                        Term.mkAnd(condition, primedCondition, sub, primedSub),
                        equal)));
            }
            case ONE: {
                // naive for now
                // exists x: S . [[x \in e]] && [[f]] && forall y: S . [[y \in e]]
                //   && [[f[x/y]]] => x = y
                List<AnnotatedVar> primed = prime(vars);
                Term primedCondition = PortusUtil.substitute(vars, primed, condition);
                Term primedSub = PortusUtil.substitute(vars, primed, sub);
                Term equal = PortusUtil.mkVarsEqual(vars, primed);
                return Term.mkExists(vars, Term.mkAnd(condition, sub,
                        Term.mkForall(primed, Term.mkImp(
                                Term.mkAnd(primedCondition, primedSub),
                                equal))));
            }
            default:
                // unsupported or not formula - NO is handled above
                throw new ErrorFatal("Unsupported ExprQt formula: " + expr.op);
        }
    }

    /**
     * Translate a list of decls from a quantifier.
     * @return Pair of (list of translated vars, condition), where the condition expresses
     *   that each variable is in the expr the decl declares it to be in. The condition must
     *   be true for the variables to be used.
     */
    private Pair<List<AnnotatedVar>, Term> translateDeclList(
            List<Decl> decls, TranslationContext context) {
        List<AnnotatedVar> translatedVars = new ArrayList<>();
        List<Term> conditions = new ArrayList<>();
        for (Decl decl : decls) {
            // Alloy typechecked that it has arity 1, so just get the first sort
            Sort sort = PortusUtil.getSorts(decl.expr, context).get(0);
            for (ExprHasName name : decl.names) {
                Var var = Term.mkVar(uniqueNameGenerator.make(name.label));
                translatedVars.add(var.of(sort));

                // Add the condition "var \in decl.expr" to restrict the domain of var
                conditions.add(recursivelyTranslate(
                        ExprElementOf.make(var, decl.expr), context));
            }
        }

        // All the conditions must be true for a set of variables to be used
        Term condition = Term.mkAnd(conditions);
        return new Pair<>(translatedVars, condition);
    }

    /** Generate a copy of `vars` with each variable suffixed with "_prime". */
    private List<AnnotatedVar> prime(List<AnnotatedVar> vars) {
        return vars.stream()
                .map(var -> Term.mkVar(uniqueNameGenerator.make(var.variable().name() + "_prime"))
                        .of(var.sort()))
                .collect(Collectors.toList());
    }

}
