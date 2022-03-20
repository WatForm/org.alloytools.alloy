package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
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
import java.util.stream.IntStream;

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

        // Make a new predicate for membership
        String memPredName = uniqueNameGenerator.make("in" + sig.label);
        sigMemberPredicates.put(sig, var -> Term.mkApp(memPredName, var));
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(memPredName, context.univSort, Sort.Bool()));

        // For top-level sigs, allocate enough elements for it in the univ sort
        if (sig.isTopLevel()) {
            context.addToUnivScope(context.scoper.sig2scope(sig));
        }

        // Translate all its children so we can translate membership in them
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

        // Generate scope constraints
        int scope = context.scoper.sig2scope(sig);
        if (context.scoper.isExact(sig)) {
            context.addAxiom(makeExactScopeAxiom(sig, scope, context));
        } else {
            context.addAxiom(makeNonExactScopeAxiom(sig, scope, context));
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

    /** Create an axiom that the sig has an exact scope of `scope`. */
    private Term makeExactScopeAxiom(Sig sig, int scope, TranslationContext context) {
        // Fortress: "exists x1, ..., xn: univ . forall x: univ . !(x1 = x2) && ...
        // && !(x1 = xn) && !(x2 = x3) && ... && !(x{n-1} = xn) && ([[x \in sig]] <=> x = x1
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
        Term xInChild = recursivelyTranslate(ExprElementOf.make(x, sig), context);
        Term implication = Term.mkIff(xInChild, Term.mkOr(eqDisjuncts));
        conjuncts.add(implication);

        // construct the decls
        List<AnnotatedVar> varDecls = Arrays.stream(vars)
                .map(var -> var.of(context.univSort))
                .collect(Collectors.toList());

        // construct the final axiom
        return Term.mkExists(varDecls, Term.mkForall(x.of(context.univSort), Term.mkAnd(conjuncts)));
    }

    /** Create an axiom that the sig has a non-exact scope of `scope`. */
    private Term makeNonExactScopeAxiom(Sig sig, int scope, TranslationContext context) {
        // Fortress: "forall x1, ..., x{n+1}: univ . [[x1 \in child]] && ... && [[x{n+1} \in child]] =>
        // x1 = x2 || .. || x1 = x{n+1} || x2 = x3 || ... || xn = x{n+1}" (KT 4.3)
        Var[] vars = new Var[scope + 1];
        for (int i = 0; i < vars.length; i++) {
            vars[i] = Term.mkVar("x" + i);
        }

        // construct the conjuncts
        List<Term> conjuncts = Arrays.stream(vars)
                .map(var -> recursivelyTranslate(ExprElementOf.make(var, sig), context))
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
                .map(var -> var.of(context.univSort))
                .collect(Collectors.toList());
        return Term.mkForall(decls, Term.mkImp(conjunction, disjunction));
    }

    /** Translate "var \in sig". */
    @Override
    public Term translate(Var var, Sig sig, TranslationContext context) {
        // if we recognize the sig, use its membership predicate
        if (!sigMemberPredicates.containsKey(sig)) {
            throw new ErrorSyntax("Unknown sig " + sig);
        }
        return sigMemberPredicates.get(sig).apply(var);
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
            case JOIN:
                return translateJoin(tuple, expr.left, expr.right, context);
            case ARROW:
                return translateCrossProduct(tuple, expr.left, expr.right, context);
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprBinary term: " + expr.op);
        }
    }

    /** Translate "tuple \in left . right". */
    private Term translateJoin(ConstList<Var> tuple, Expr left, Expr right, TranslationContext context) {
        // Naive join implementation without optimizations (see KT figure 4.11).
        // [[(x1,...,xn) \in e1 . e2]] := exists y: univ . [[(x1,...,xm,y) \in e1]] &&
        //   [[(y,x{m+1},...,xn) \in e2]] where arity(e1) = m+1 and arity(e2) = n-m+1 and m<n
        Var y = Term.mkVar(uniqueNameGenerator.make("y"));

        // build up the tuples we'll recurse on
        int partitionIdx = left.type().arity() - 1; // so that adding y gives the arity
        List<Var> leftSubTuple = new ArrayList<>(tuple.subList(0, partitionIdx));
        leftSubTuple.add(y); // append y to make (x1, ..., xm, y)
        List<Var> rightSubTuple = new ArrayList<>(tuple.subList(partitionIdx, tuple.size()));
        rightSubTuple.add(0, y); // prepend y to make (y, x{m+1}, ..., xn)

        return Term.mkExists(y.of(context.univSort), Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(ConstList.make(leftSubTuple), left), context),
                recursivelyTranslate(ExprElementOf.make(ConstList.make(rightSubTuple), right), context)));
    }

    /** Translate "tuple \in left->right". */
    private Term translateCrossProduct(
            ConstList<Var> tuple, Expr left, Expr right, TranslationContext context) {
        // [[(x1,...,xn \in e1->e2]] := [[(x1,...,xm) \in e1]] && [[(x{m+1},...,xn) \in e2]]
        // where arity(e1) = m and arity(e2) = n-m
        if (left.type().arity() + right.type().arity() != tuple.size()) {
            throw new ErrorFatal("Cross product arities do not match!");
        }

        List<Var> leftSubTuple = new ArrayList<>(tuple.subList(0, left.type().arity()));
        List<Var> rightSubTuple = new ArrayList<>(tuple.subList(left.type().arity(), tuple.size()));

        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(ConstList.make(leftSubTuple), left), context),
                recursivelyTranslate(ExprElementOf.make(ConstList.make(rightSubTuple), right), context));
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
            case IN:
            case EQUALS:
                return translateInEq(expr.op, expr.left, expr.right, context);
            case NOT_IN: {
                // interpret as "not (left in right)"
                Expr interpretation = expr.left.in(expr.right).not();
                return recursivelyTranslate(interpretation, context);
            }
            case NOT_EQUALS: {
                // interpret as "not (left = right)"
                Expr interpretation = expr.left.equal(expr.right).not();
                return recursivelyTranslate(interpretation, context);
            }
            case AND:
            case OR:
                // confusingly, AND and OR aren't real ExprBinary ops
                throw new ErrorFatal("AND and OR should be ExprLists!");
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprBinary formula: " + expr.op);
        }
    }

    /** Translate the formula "e1 in e2" or "e1 = e2". */
    private Term translateInEq(ExprBinary.Op op, Expr e1, Expr e2, TranslationContext context) {
        // KT figure 4.9: [[e1 in e2]] := forall x1: S1, ..., xn: Sn .
        //   [[(x1, ..., xn) \in e1]] => [[(x1, ..., xn) \in e2]]
        // and [[e1 = e2]] := forall x1: S1, ..., sn: Sn .
        //   [[(x1, ..., xn) \in e1]] <=> [[(x1, ..., xn) \in e2]]
        // typechecker ensured arities are the same, make sure sort are the same
        assert e1.type().arity() == e2.type().arity();

        // create the variables
        List<AnnotatedVar> varDecls = IntStream.range(0, e1.type().arity())
                .mapToObj(idx ->Term.mkVar(uniqueNameGenerator.make("x" + idx))
                        .of(context.univSort))
                .collect(Collectors.toList());
        ConstList<Var> vars = ConstList.make(varDecls.stream()
                .map(AnnotatedVar::variable)
                .collect(Collectors.toList()));

        Term inE1 = recursivelyTranslate(ExprElementOf.make(vars, e1), context);
        Term inE2 = recursivelyTranslate(ExprElementOf.make(vars, e2), context);
        Term condition;
        if (op == ExprBinary.Op.IN) {
            condition = Term.mkImp(inE1, inE2);
        } else { // ExprBinary.Op.EQUALS
            condition = Term.mkIff(inE1, inE2);
        }

        return Term.mkForall(varDecls, condition);
    }

    /** Translate an ExprUnary formula. */
    @Override
    public Term translate(ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOT:
                // see KT figure 4.6
                return Term.mkNot(
                        recursivelyTranslate(expr.sub, context));
            case NOOP:
                // no-op: ignore it
                return recursivelyTranslate(expr.deNOP(), context);
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprUnary formula: " + expr.op);
        }
    }

    @Override
    public Term translate(ConstList<Var> tuple, ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOOP:
                // no-op: ignore it
                return recursivelyTranslate(ExprElementOf.make(tuple, expr.deNOP()), context);
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprUnary term: " + expr.op);
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
    // TODO: COMPREHENSION, SUM - terms, not formulas
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
        Pair<Map<String, AnnotatedVar>, Term> varsAndCond = translateDeclList(expr.decls, context);
        Map<String, AnnotatedVar> namesToVars = varsAndCond.a;
        List<AnnotatedVar> vars = new ArrayList<>(namesToVars.values());
        Term condition = varsAndCond.b;

        // Process subformula - Fortress vars were added to the lexical scope in translateDeclList()
        Term sub = recursivelyTranslate(expr.sub, context);

        // Remove the vars from the lexical scope since it's done
        for (String alloyVarName : namesToVars.keySet()) {
            context.removeVarMapping(alloyVarName);
        }

        // Process the formula itself - see KT figure 4.6
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
                vars.addAll(primed); // add both at the same time
                return Term.mkForall(vars, Term.mkImp(
                        Term.mkAnd(condition, primedCondition, sub, primedSub),
                        equal));
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

    /** Translate "var \in expr", where expr is an ExprVar. */
    @Override
    public Term translate(Var var, ExprVar expr, TranslationContext context) {
        // KT figure 4.12: [[x \in v]] := x = v
        return Term.mkEq(var, checkAndMapVarName(expr.label, context));
    }

    /** Translate "tuple \in expr", where expr is an ExprConstant. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprConstant expr, TranslationContext context) {
        switch (expr.op) {
            case IDEN:
                return translateIden(tuple, context);
            case EMPTYNESS:
                // "tuple \in none" is always false
                return Term.mkBottom();
            default:
                throw new ErrorFatal("Unsupported ExprConstant: " + expr);
        }
    }

    /** Translate "tuple \in iden". */
    private Term translateIden(ConstList<Var> tuple, TranslationContext context) {
        // KT figure 4.12: [[(x1, x2) \in iden]] := x1 = x2
        // note that this works even for incompatible top-level sigs since we use a universal sort
        if (tuple.size() != 2) {
            throw new ErrorFatal("iden expects arity 2, but got " + tuple.size());
        }
        return Term.mkEq(tuple.get(0), tuple.get(1));
    }

    /** Map an Alloy variable name to a Fortress var, or throw an error. */
    private Var checkAndMapVarName(String label, TranslationContext context) {
        // the Alloy variable must be mapped to a Fortress var in the current lexical scope
        if (!context.hasVarMapping(label)) {
            throw new ErrorSyntax("Unknown variable name " + label);
        }
        return context.getVarMapping(label);
    }

    /**
     * Translate a list of decls from a quantifier.
     * @return Pair of (map of Alloy variable names to translated vars, condition), where the
     *   condition expresses that each variable is in the expr the decl declares it to be in.
     *   The condition must be true for the variables to be used.
     * @apiNote The variable names are added to the context's var mapping and must be cleaned up after.
     */
    private Pair<Map<String, AnnotatedVar>, Term> translateDeclList(
            List<Decl> decls, TranslationContext context) {
        Map<String, AnnotatedVar> namesToVars = new HashMap<>();
        List<Term> conditions = new ArrayList<>();
        for (Decl decl : decls) {
            // Alloy typechecked that it has arity 1
            for (ExprHasName name : decl.names) {
                Var var = Term.mkVar(uniqueNameGenerator.make(name.label));
                namesToVars.put(name.label, var.of(context.univSort));

                // Add it to the lexical scope in order to translate the condition
                context.addVarMapping(name.label, var);

                // Ensure decl.expr is ONEOF: we don't support other multiplicities in quantifiers (yet)
                // TODO: try to skolemize it like Kodkod does?
                if (decl.expr.mult() != ExprUnary.Op.ONEOF) {
                    throw new ErrorFatal("Unsupported quantifier multiplicity for Fortress: "
                            + decl.expr.mult());
                }

                // Unwrap the expression from its multiplicity (and any NOOPs)
                // We know this is an ExprUnary because decl.expr.mult() returned ONEOF,
                // which it only does if there's an ExprUnary somewhere in the chain.
                ExprUnary wrappedDeclExpr = (ExprUnary) decl.expr.deNOP();
                Expr declExpr = wrappedDeclExpr.sub;

                // Add the condition "var \in declExpr" to restrict the domain of var
                conditions.add(recursivelyTranslate(
                        ExprElementOf.make(var, declExpr), context));
            }
        }

        // All the conditions must be true for a set of variables to be used
        Term condition = Term.mkAnd(conditions);
        return new Pair<>(namesToVars, condition);
    }

    /** Generate a copy of `vars` with each variable suffixed with "_prime". */
    private List<AnnotatedVar> prime(List<AnnotatedVar> vars) {
        return vars.stream()
                .map(var -> Term.mkVar(uniqueNameGenerator.make(var.variable().name() + "_prime"))
                        .of(var.sort()))
                .collect(Collectors.toList());
    }

}
