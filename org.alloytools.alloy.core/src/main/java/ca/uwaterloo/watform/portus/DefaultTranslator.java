package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.DomainElement;
import fortress.msfol.FuncDecl;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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
    // Represent it by a Java function taking "x" to "inA(x)".
    private final Map<Sig, Function<Var, Term>> sigMemberPredicates = new HashMap<>();

    // Relation predicates for each field (see KT 4.2).
    // Note: no function optimization yet/in this class.
    // Represent relations by a Java function taking "x1,...,xn" to "f(x1,...,xn)".
    private final Map<Sig.Field, Function<List<Var>, Term>> relationPredicates = new HashMap<>();

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
        return Term.mkTop();
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
        // Special cases: builtin sigs
        if (sig.builtin) {
            if (sig.equals(Sig.UNIV)) {
                // "var \in univ" is always true
                return Term.mkTop();
            } else if (sig.equals(Sig.STRING)) {
                // TODO - implement strings for real
                return Term.mkBottom();
            } else {
                throw new ErrorFatal("Unsupported builtin sig: " + sig);
            }
        }

        // if we recognize the sig, use its membership predicate
        if (!sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Unknown sig " + sig);
        }
        return sigMemberPredicates.get(sig).apply(var);
    }

    /** Translate a field declaration inside a sig. */
    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        // Make a new predicate for the field relation (no function optimization yet).
        String relName = uniqueNameGenerator.make(field.label);
        relationPredicates.put(field, vars -> {
            if (vars.size() != field.type().arity()) {
                throw new ErrorFatal("Internal error: bad field relation predicate arity.");
            }
            return Term.mkApp(relName, vars);
        });

        // the predicate signature is (univ)^n -> Bool, where n is the field arity
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(relName,
                Collections.nCopies(field.type().arity(), context.univSort), Sort.Bool()));

        // constrain the domain of the field: see KT 4.2 (page 29)
        context.addAxiom(makeFieldDomainConstraint(field, context));

        // just return Top because the returned term doesn't matter for a field declaration
        return Term.mkTop();
    }

    /** Create an axiom asserting that the field's relation stays within its domain. */
    private Term makeFieldDomainConstraint(Sig.Field field, TranslationContext context) {
        // See KT 4.2 (page 29).
        // for "sig A {f: e}", translate to [[f in A->e]] (roughly)
        Expr domainExpr = getFieldDomainExpr(field);
        return recursivelyTranslate(field.in(domainExpr), context);
    }

    /** Get the expression bounding the field's domain: e.g. for "sig A {f: B}", return A->one B. */
    private Expr getFieldDomainExpr(Sig.Field field) {
        // Choose the appropriate arrow according to the field expr's multiplicity.
        Expr declared = field.decl().expr.deNOP(); // what it's declared as: e.g. in "f: B", this is B
        ExprUnary.Op mult = declared.mult();
        if (declared.mult == 1) { // 1 means it's a multiplicity contraint like "ONEOF", "SOMEOF"
            // Strip the multiplicity constraint
            declared = ((ExprUnary) declared).sub;
        }
        switch (mult) {
            case ONEOF:
                return field.sig.any_arrow_one(declared);
            case LONEOF:
                return field.sig.any_arrow_lone(declared);
            case SOMEOF:
                return field.sig.any_arrow_some(declared);
            // TODO: we don't support EXACTLYOF, is it needed?
            case SETOF:
            default:
                return field.sig.product(declared);
        }
    }

    @Override
    public Term translate(ConstList<Var> tuple, Sig.Field field, TranslationContext context) {
        // if we recognize the field, use its relation
        if (!relationPredicates.containsKey(field)) {
            throw new ErrorFatal("Unknown field: " + field);
        }
        return relationPredicates.get(field).apply(tuple);
    }

    /** Translate "tuple \in expr", where expr is an ExprBinary term. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprBinary expr, TranslationContext context) {
        // Both sides or neither side should be integers, we don't support mixing
        checkAllInt(expr.left, expr.right);

        switch (expr.op) {
            case PLUS:
                return translateUnion(tuple, expr.left, expr.right, context);
            case INTERSECT:
                return translateIntersection(tuple, expr.left, expr.right, context);
            case MINUS:
                return translateSetDifference(tuple, expr.left, expr.right, context);
            case JOIN:
                return translateJoin(tuple, expr.left, expr.right, context);
            case ARROW:
                return translateCrossProduct(tuple, expr.left, expr.right, context);
            case DOMAIN:
                return translateDomainRestriction(tuple, expr.left, expr.right, context);
            case RANGE:
                return translateRangeRestriction(tuple, expr.left, expr.right, context);
            case PLUSPLUS:
                return translateOverride(tuple, expr.left, expr.right, context);
            case IPLUS:
            case IMINUS:
            case MUL:
            case DIV:
            case REM:
                if (tuple.size() != 1) {
                    throw new ErrorFatal("The arity of an arithmetic operation must be 1.");
                }
                return Term.mkEq(tuple.get(0), translateArithmeticOperation(
                        expr.op, expr.left, expr.right, context));
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprBinary term: " + expr.op);
        }
    }

    /** Translate "tuple \in left + right". */
    private Term translateUnion(ConstList<Var> tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkOr(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    /** Translate "tuple \in left & right". */
    private Term translateIntersection(
            ConstList<Var> tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    private Term translateSetDifference(
            ConstList<Var> tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                Term.mkNot(recursivelyTranslate(ExprElementOf.make(tuple, right), context)));
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

    /** Translate the formula "tuple \in domain <: expr". */
    private Term translateDomainRestriction(
            ConstList<Var> tuple, Expr domain, Expr expr, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in domain <: expr]] := [[x1 \in domain]] && [[(x1,...,xn) \in expr]]
        // where arity(domain) = 1 and arity(expr) = n
        if (domain.type().arity() != 1) {
            throw new ErrorFatal("The left-hand side of a domain restriction must have arity 1.");
        }

        ConstList<Var> firstVar = ConstList.make(Collections.singletonList(tuple.get(0)));

        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(firstVar, domain), context),
                recursivelyTranslate(ExprElementOf.make(tuple, expr), context));
    }

    /** Translate the formula "tuple \in expr :> range". */
    private Term translateRangeRestriction(
            ConstList<Var> tuple, Expr expr, Expr range, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in expr :> range]] := [[(x1,...,xn) \in expr]] && [[xn \in range]]
        // where arity(expr) = n and arity(range) = 1
        if (range.type().arity() != 1) {
            throw new ErrorFatal("The right-hand side of a range restriction must have arity 1.");
        }

        ConstList<Var> lastVar = ConstList.make(Collections.singletonList(tuple.get(tuple.size() - 1)));

        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, expr), context),
                recursivelyTranslate(ExprElementOf.make(lastVar, range), context));
    }

    /** Translate the formula "tuple \in base ++ override". */
    private Term translateOverride(
            ConstList<Var> tuple, Expr base, Expr override, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in base ++ override]] := [[(x1,...,xn) \in override]]
        // || ([[(x1,...,xn \in base]] && !(exists y2,...,yn . [[(x1,y2,...,yn) \in override]]))
        // where arity(base) = arity(override) = n
        int arity = base.type().arity();
        if (override.type().arity() != arity) {
            throw new ErrorFatal("The arities of the sides of '++' must match.");
        }

        // Special case: arity = 1, avoid having zero elements for y2,...,yn.
        // Translate [[x \in base ++ override]] := [[x \in base + override]] to take advantage
        // of any optimizations for union.
        if (arity == 1) {
            return recursivelyTranslate(ExprElementOf.make(tuple, base.plus(override)), context);
        }

        // translate [[(x1,...,xn) \in base]] and [[(x1,...,xn) \in override]]
        Term inBase = recursivelyTranslate(ExprElementOf.make(tuple, base), context);
        Term inOverride = recursivelyTranslate(ExprElementOf.make(tuple, override), context);

        // build up the vars x1,y2,...,yn and the annotated vars y2,...,yn
        List<AnnotatedVar> annotatedVars = new ArrayList<>(arity - 1);
        List<Var> overrideVars = new ArrayList<>(arity);
        overrideVars.add(tuple.get(0));
        for (int i = 0; i < arity - 1; i++) {
            Var y = Term.mkVar(uniqueNameGenerator.make("y" + i));
            overrideVars.add(y);
            annotatedVars.add(y.of(context.univSort));
        }

        // translate [[(x1,y2,...,yn) \in override]]
        Term firstInOverride = recursivelyTranslate(
                ExprElementOf.make(ConstList.make(overrideVars), override), context);

        return Term.mkOr(inOverride, Term.mkAnd(
                inBase, Term.mkNot(Term.mkExists(annotatedVars, firstInOverride))));
    }

    /** Translate an ExprBinary formula or integer-valued expression. */
    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        if (PortusUtil.isDeclarationFormula(expr)) {
            return translateDeclarationFormula(expr.left, (ExprBinary) expr.right, context);
        }

        // Both sides or neither side should be integers, we don't support mixing
        checkAllInt(expr.left, expr.right);

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
            case LT:
            case LTE:
            case GT:
            case GTE:
            case NOT_LT:
            case NOT_LTE:
            case NOT_GT:
            case NOT_GTE:
                return translateArithmeticComparison(expr.op, expr.left, expr.right, context);
            case IPLUS:
            case IMINUS:
            case MUL:
            case DIV:
            case REM:
                // these are integer expressions and not formulas
                return translateArithmeticOperation(expr.op, expr.left, expr.right, context);
            case AND:
            case OR:
                // confusingly, AND and OR aren't real ExprBinary ops
                throw new ErrorFatal("AND and OR should be ExprLists!");
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprBinary formula: " + expr.op);
        }
    }

    /** Translate "expr in arrow", where arrow has a multiplicity or one of its children does. */
    private Term translateDeclarationFormula(Expr expr, ExprBinary arrow, TranslationContext context) {
        // From Software Abstractions (Jackson), 3.6.3--3.6.5:
        // [[expr in A M->N B]] := [[expr in A->B]] && [[all a: A | N a.expr]] && [[all b: B | M expr.b]]
        // There might be optimization opportunities here for nested multiplicity arrows.
        assert arrow.op.isArrow;

        // find the multiplicities of both sides
        ExprUnary.Op leftMult = PortusUtil.getArrowLeftMultiplicity(arrow.op);
        ExprUnary.Op rightMult = PortusUtil.getArrowRightMultiplicity(arrow.op);
        assert leftMult != null && rightMult != null;

        // translate [[expr in A->B]] without multiplicities
        Expr plainArrow = PortusUtil.stripArrowMultiplicities(arrow);
        Term exprInArrow = recursivelyTranslate(expr.in(plainArrow), context);

        List<Term> conjuncts = new ArrayList<>();
        conjuncts.add(exprInArrow);

        // translate [[all a: A | N a.expr]] where N is the right multiplicity
        if (rightMult != ExprUnary.Op.NOOP) {
            Decl a = arrow.left.oneOf("a");
            Expr multBound = rightMult.make(null, a.get().join(expr)).forAll(a);
            conjuncts.add(recursivelyTranslate(multBound, context));
        }

        // translate [[all b: B | M expr.b]] where M is the left multiplicity
        if (leftMult != ExprUnary.Op.NOOP) {
            Decl b = arrow.right.oneOf("b");
            Expr multBound = leftMult.make(null, expr.join(b.get())).forAll(b);
            conjuncts.add(recursivelyTranslate(multBound, context));
        }

        // handle nested arrows
        if (PortusUtil.isDeclarationFormulaArrow(arrow.right)) {
            // add [[all a: A | a.expr in B]]
            Decl a = arrow.left.oneOf("a");
            Expr nestedBound = a.get().join(expr).in(arrow.right).forAll(a);
            conjuncts.add(recursivelyTranslate(nestedBound, context));
        }
        if (PortusUtil.isDeclarationFormulaArrow(arrow.left)) {
            // add [[all b: B | expr.b in A]]
            Decl b = arrow.right.oneOf("b");
            Expr nestedBound = expr.join(b.get()).in(arrow.left).forAll(b);
            conjuncts.add(recursivelyTranslate(nestedBound, context));
        }

        return Term.mkAnd(conjuncts);
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
        boolean isInt = checkAllInt(e1, e2);
        List<AnnotatedVar> varDecls = IntStream.range(0, e1.type().arity())
                .mapToObj(idx ->Term.mkVar(uniqueNameGenerator.make("x" + idx))
                        .of(isInt ? Sort.Int() : context.univSort))
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

    /** Translate "lhs op rhs", where op is an arithmetic comparison like <, >, =<, >=.  */
    private Term translateArithmeticComparison(ExprBinary.Op op, Expr lhs, Expr rhs, TranslationContext context) {
        ensureAllInt(op + " requires both sides to be integers!", lhs, rhs);

        Term left = recursivelyTranslate(lhs, context);
        Term right = recursivelyTranslate(rhs, context);
        switch (op) {
            case LT:
            case NOT_GTE:
                return Term.mkLT(left, right);
            case LTE:
            case NOT_GT:
                return Term.mkLE(left, right);
            case GT:
            case NOT_LTE:
                return Term.mkGT(left, right);
            case GTE:
            case NOT_LT:
                return Term.mkGE(left, right);
            default:
                throw new ErrorFatal("Unsupported arithmetic comparison operator: " + op);
        }
    }

    /** Translate "lhs op rhs", where op is an arithmetic operation. */
    private Term translateArithmeticOperation(ExprBinary.Op op, Expr lhs, Expr rhs, TranslationContext context) {
        ensureAllInt(op + " requires both sides to be integer expressions!", lhs, rhs);

        Term left = recursivelyTranslate(lhs, context);
        Term right = recursivelyTranslate(rhs, context);
        switch (op) {
            case IPLUS:
                return Term.mkPlus(left, right);
            case IMINUS:
                return Term.mkSub(left, right);
            case MUL:
                return Term.mkMult(left, right);
            case DIV:
                return Term.mkDiv(left, right);
            case REM:
                return Term.mkMod(left, right);
            default:
                throw new ErrorFatal("Unsupported arithmetic operation: " + op);
        }
    }

    /** Translate the formula "f1 => f2 else f3". */
    @Override
    public Term translate(ExprITE expr, TranslationContext context) {
        // use Fortress's built-in if-then-else
        Term cond = recursivelyTranslate(expr.cond, context);
        Term left = recursivelyTranslate(expr.left, context);
        Term right = recursivelyTranslate(expr.right, context);
        return Term.mkIfThenElse(cond, left, right);
    }

    /** Translate the formula "tuple \in (f => e1 else e2)". */
    @Override
    public Term translate(ConstList<Var> tuple, ExprITE expr, TranslationContext context) {
        // Similar to the above: "IfThenElse([[f]], [[tuple \in e1]], [[tuple \in e2]])"
        Term cond = recursivelyTranslate(expr.cond, context);
        Term left = recursivelyTranslate(ExprElementOf.make(tuple, expr.left), context);
        Term right = recursivelyTranslate(ExprElementOf.make(tuple, expr.right), context);
        return Term.mkIfThenElse(cond, left, right);
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
            case NO:
                return translateQuantifiedExpr(ExprQt.Op.NO, expr.sub, context);
            case LONE:
                return translateQuantifiedExpr(ExprQt.Op.LONE, expr.sub, context);
            case ONE:
                return translateQuantifiedExpr(ExprQt.Op.ONE, expr.sub, context);
            case SOME:
                return translateQuantifiedExpr(ExprQt.Op.SOME, expr.sub, context);
            case CAST2INT:
            case CAST2SIGINT:
                // These appear to be for internal use in the Alloy->Kodkod translation, ignore for now.
                return recursivelyTranslate(expr.sub, context);
            case CARDINALITY:
                return translateCardinality(expr.sub, context);
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprUnary formula: " + expr.op);
        }
    }

    /** Translate "Q e", where Q is one of {one, lone, some, no} and e is an expression. */
    private Term translateQuantifiedExpr(ExprQt.Op quantifier, Expr expr, TranslationContext context) {
        // "Q e" is equivalent to "Q x: e | true", so translate as such for simplicity
        Decl x = expr.oneOf("x");
        Expr formula = quantifier.make(null, null, Collections.singletonList(x), ExprConstant.TRUE);
        return recursivelyTranslate(formula, context);
    }

    /** Translate "#e", as an integer expression. */
    private Term translateCardinality(Expr expr, TranslationContext context) {
        // Equivalent to "sum x: e | 1", so translate as such for simplicity
        Expr sum = ExprConstant.ONE.sumOver(expr.oneOf("x"));
        return recursivelyTranslate(sum, context);
    }

    /** Translate "tuple \in expr", where expr is an ExprUnary formula. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOOP:
                // no-op: ignore it
                return recursivelyTranslate(ExprElementOf.make(tuple, expr.deNOP()), context);
            case TRANSPOSE:
                return translateTranspose(tuple, expr.sub, context);
            case CARDINALITY:
                return translateInIntExpr(tuple, expr, context);
            case CAST2INT:
            case CAST2SIGINT:
                // These appear to be for internal use in the Alloy->Kodkod translation, ignore for now.
                return recursivelyTranslate(ExprElementOf.make(tuple, expr.sub), context);
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprUnary term: " + expr.op);
        }
    }

    /** Translate "tuple \in ~sub". */
    private Term translateTranspose(ConstList<Var> tuple, Expr sub, TranslationContext context) {
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Transpose argument must have arity 2");
        }

        // swap the variables in the tuple - see KT figure 4.11
        ConstList<Var> swapped = ConstList.make(Arrays.asList(tuple.get(1), tuple.get(0)));
        return recursivelyTranslate(ExprElementOf.make(swapped, sub), context);
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
            // note that an empty AND list is always true, and an empty OR list is always false
            case AND:
                return translatedArgs.size() == 0 ? Term.mkTop() : Term.mkAnd(translatedArgs);
            case OR:
                return translatedArgs.size() == 0 ? Term.mkBottom() : Term.mkOr(translatedArgs);
            default:
                // we don't yet support DISJOINT or TOTALORDER
                throw new ErrorFatal("Unsupported ExprList formula: " + expr.op);
        }
    }

    /** Translate an ExprQt formula. */
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
            context.removeMapping(alloyVarName);
        }

        // Process the formula itself - see KT figure 4.6
        switch (expr.op) {
            case ALL:
                // forall x1: S, ..., xn: S . [[x1 \in e1]] && ... && [[xn \in en]] => [[sub]]
                return Term.mkForall(vars, Term.mkImp(condition, sub));
            case SOME:
                // exists x1: S, ..., xn: S . [[x1 \in e1]] && ... && [[xn \in en]] && [[sub]]
                return Term.mkExists(vars, Term.mkAnd(condition, sub));
            case LONE: {
                // naive for now
                // forall x, y: S . [[x \in e]] && [[y \in e]] && [[f]] && [[f[x/y]]] => x = y
                List<AnnotatedVar> primed = prime(vars);
                Term primedCondition = PortusUtil.substituteVars(vars, primed, condition);
                Term primedSub = PortusUtil.substituteVars(vars, primed, sub);
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
                Term primedCondition = PortusUtil.substituteVars(vars, primed, condition);
                Term primedSub = PortusUtil.substituteVars(vars, primed, sub);
                Term equal = PortusUtil.mkVarsEqual(vars, primed);
                return Term.mkExists(vars, Term.mkAnd(condition, sub,
                        Term.mkForall(primed, Term.mkImp(
                                Term.mkAnd(primedCondition, primedSub),
                                equal))));
            }
            case SUM:
                return translateSum(sub, condition, vars, context);
            default:
                // unsupported or not formula - NO is handled above
                throw new ErrorFatal("Unsupported ExprQt formula: " + expr.op);
        }
    }

    // Translate "sum x: e | f" where sub translates [[f]] and condition translates [[x \in e]].
    private Term translateSum(Term sub, Term condition, List<AnnotatedVar> vars, TranslationContext context) {
        // naive for now: manually expand "sum y: univ | [[y \in e]] => [[f[y/x]]] else 0"
        // nest the additions naively left-to-right: ((((1 + 1) + 1) + 1) + ...)
        List<Sort> sorts = new ArrayList<>();
        List<Integer> sortScopes = new ArrayList<>();
        List<Integer> currentIdxs = new ArrayList<>(); // indexes of the current domain elements
        for (AnnotatedVar var : vars) {
            sorts.add(var.sort());
            sortScopes.add(var.sort() == context.univSort ? context.getUnivScope() : context.getIntScope());
            currentIdxs.add(1);
        }

        Term result = null;
        do {
            // substitute with the domain elements for each combination
            List<DomainElement> domainElements = IntStream.range(0, vars.size())
                    .mapToObj(i -> DomainElement.apply(currentIdxs.get(i), sorts.get(i)))
                    .collect(Collectors.toList());
            Term domElemCondition = PortusUtil.substitute(vars, domainElements, condition);
            Term domElemSub = PortusUtil.substitute(vars, domainElements, sub);

            // add "condition => sub else 0" to the result
            Term addend = Term.mkIfThenElse(domElemCondition, domElemSub, IntegerLiteral.apply(0));
            if (result == null) {
                result = addend;
            } else {
                result = Term.mkPlus(result, addend);
            }
        } while (PortusUtil.nextCombination(currentIdxs, sortScopes));
        return result;
    }

    /** Translate "tuple \in expr", where expr is an ExprQt. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprQt expr, TranslationContext context) {
        switch (expr.op) {
            case COMPREHENSION:
                return translateComprehension(tuple, expr, context);
            case SUM:
                return translateInIntExpr(tuple, expr, context);
            default:
                // unsupported or not expression
                throw new ErrorFatal("Unsupported ExprQt expression: " + expr.op);
        }
    }

    /** Translate "tuple \in expr", where expr is a comprehension ExprQt. */
    private Term translateComprehension(ConstList<Var> tuple, ExprQt expr, TranslationContext context) {
        // [[(x1,...,xn) \in {y1: e1, ..., yn: en | f(y1,...,yn)}]] :=
        // [[x1 \in e1]] && ... && [[xn \in en]] && [[f(y1,...,yn)]] where yi is mapped to xi
        // First, check the arity is correct
        if (tuple.size() != expr.count()) {
            throw new ErrorSyntax("Mismatched arity for comprehension expression!");
        }

        // Pair the vars and decls/names
        List<Pair<Var, Pair<Decl, ExprHasName>>> varsAndDecls = new ArrayList<>();
        int tupleIdx = 0;
        for (Decl decl : expr.decls) {
            for (ExprHasName name : decl.names) {
                Var var = tuple.get(tupleIdx);
                varsAndDecls.add(new Pair<>(var, new Pair<>(decl, name)));
                tupleIdx++;
            }
        }

        List<Term> conjuncts = new ArrayList<>();

        // Generate each [[xi \in ei]] conjunct
        for (Pair<Var, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
            Var var = varAndDecl.a;
            Decl decl = varAndDecl.b.a;
            // Unwrap the expression from its multiplicity (and any NOOPs)
            Expr declExpr = decl.expr.deNOP();
            if (declExpr.mult == 1) {
                // We know this is an ExprUnary because decl.expr.mult() must return ONEOF,
                // because ExprQt doesn't allow comprehension decls to have other multiplicities.
                ExprUnary wrappedDeclExpr = (ExprUnary) declExpr;
                declExpr = wrappedDeclExpr.sub;
            }
            Expr conjunct = ExprElementOf.make(ConstList.make(1, var), declExpr);
            conjuncts.add(recursivelyTranslate(conjunct, context));
        }

        // Map each yi to xi - do this after generating conjuncts to avoid any interference
        for (Pair<Var, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
            Var var = varAndDecl.a;
            ExprHasName name = varAndDecl.b.b;
            context.addVarMapping(name.label, var);
        }

        // Map [[f(y1,...,yn)]]
        conjuncts.add(recursivelyTranslate(expr.sub, context));

        // Unmap all the yi's
        for (Pair<Var, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
            ExprHasName name = varAndDecl.b.b;
            context.removeMapping(name.label);
        }

        return Term.mkAnd(conjuncts);
    }

    /** Translate an ExprLet formula. */
    @Override
    public Term translate(ExprLet let, TranslationContext context) {
        // Bind the variable in the context, translate the subformula, and remove the variable.
        context.addLetMapping(let.var.label, let.expr);
        Term result = recursivelyTranslate(let.sub, context);
        context.removeMapping(let.var.label);
        return result;
    }

    /** Translate "tuple \in expr", where expr is an ExprVar. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            @SuppressWarnings("ConstantConditions") // IntelliJ gives a false positive nullable warning
            Expr mapped = ExprElementOf.make(tuple, context.getLetMapping(expr.label));
            return recursivelyTranslate(mapped, context);
        }

        // KT figure 4.12: [[x \in v]] := x = v
        if (tuple.size() != 1) {
            throw new ErrorFatal("Wrong arity for ExprVar!");
        }
        return Term.mkEq(tuple.get(0), checkAndMapVarName(expr.label, context));
    }

    /** Translate an ExprVar integer expression. */
    @Override
    public Term translate(ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            return recursivelyTranslate(context.getLetMapping(expr.label), context);
        }
        return checkAndMapVarName(expr.label, context);
    }

    /** Translate an ExprConstant formula/integer expression. */
    @Override
    public Term translate(ExprConstant expr, TranslationContext context) {
        // The only ExprConstant formulas are TRUE and FALSE - we generate them in recursive translations.
        // Also translate numbers since they're integer expressions (standalone).
        switch (expr.op) {
            case TRUE:
                return Term.mkTop();
            case FALSE:
                return Term.mkBottom();
            case NUMBER:
                return IntegerLiteral.apply(expr.num);
            default:
                throw new ErrorFatal("Unsupported ExprConstant formula/int expression: " + expr);
        }
    }

    /** Translate "tuple \in expr", where expr is an ExprConstant. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprConstant expr, TranslationContext context) {
        switch (expr.op) {
            case IDEN:
                return translateIden(tuple);
            case EMPTYNESS:
                // "tuple \in none" is always false
                return Term.mkBottom();
            case NUMBER:
                return translateInIntExpr(tuple, expr, context);
            default:
                throw new ErrorFatal("Unsupported ExprConstant expression: " + expr);
        }
    }

    /** Translate "tuple \in iden". */
    private Term translateIden(ConstList<Var> tuple) {
        // KT figure 4.12: [[(x1, x2) \in iden]] := x1 = x2
        // note that this works even for incompatible top-level sigs since we use a universal sort
        if (tuple.size() != 2) {
            throw new ErrorFatal("iden expects arity 2, but got " + tuple.size());
        }
        return Term.mkEq(tuple.get(0), tuple.get(1));
    }

    /** Translate a predicate or integer-valued function call. */
    @Override
    public Term translate(ExprCall call, TranslationContext context) {
        return translateCall(call.fun.getBody(), call, context);
    }

    /** Translate "tuple \in call", where call is a function call. */
    @Override
    public Term translate(ConstList<Var> tuple, ExprCall call, TranslationContext context) {
        return translateCall(ExprElementOf.make(tuple, call.fun.getBody()), call, context);
    }

    /** Translate a pred or fun, but where "body" is the expr to recursively translate in scope. */
    private Term translateCall(Expr body, ExprCall call, TranslationContext context) {
        // Just naively substitute it.
        // TODO: handle recursion - currently we loop forever
        if (call.args.size() != call.fun.count()) {
            throw new ErrorFatal("Wrong number of arguments to predicate or function!");
        }

        // Add the parameter mappings to the context.
        for (int i = 0; i < call.fun.count(); i++) {
            Expr arg = call.args.get(i);
            ExprVar param = call.fun.get(i);
            context.addLetMapping(param.label, arg);
        }

        Term result = recursivelyTranslate(body, context);

        // Remove all the parameters from the context.
        for (int i = 0; i < call.fun.count(); i++) {
            ExprVar param = call.fun.get(i);
            context.removeMapping(param.label);
        }
        return result;
    }

    private Term translateInIntExpr(ConstList<Var> tuple, Expr intExpr, TranslationContext context) {
        if (tuple.size() != 1) {
            throw new ErrorSyntax("Int expression '" + intExpr + "' requires arity 1");
        }
        return Term.mkEq(tuple.get(0), recursivelyTranslate(intExpr, context));
    }

    /**
     * Verify that either all of `exprs` are Int exprs or none are, and return whether they all are
     * (and there's at least one expr specified - on empty input return false).
     */
    private boolean checkAllInt(Expr... exprs) {
        boolean allInt = false;
        boolean decided = false;
        for (Expr expr : exprs) {
            boolean isInt = expr.type().is_int() // Int is the first sig in one of the product types
                    && expr.type().size() == 1   // and there's only one product type
                    && expr.type().arity() == 1; // and it only has one sig
            if (decided) {
                if (isInt != allInt) {
                    throw new ErrorFatal("Portus does not support sets with integers and other atoms mixed!");
                }
            } else {
                decided = true;
                allInt = isInt;
            }
        }
        return allInt;
    }

    /** Like checkAllIns, but throw an error if they aren't all integer expressions. */
    private void ensureAllInt(String message, Expr... exprs) {
        boolean allInts = checkAllInt(exprs);
        if (!allInts) {
            throw new ErrorFatal(message);
        }
    }

    /** Map an Alloy variable name to a Fortress term, or throw an error. */
    private Term checkAndMapVarName(String label, TranslationContext context) {
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
                Expr declExpr = wrappedDeclExpr.sub.deNOP();

                // Create var and it to the lexical scope to translate the condition and subformula
                Var var = Term.mkVar(uniqueNameGenerator.make(name.label));
                context.addVarMapping(name.label, var);

                // Use Int if it's an integer expression, otherwise univ
                Sort varSort = checkAllInt(declExpr) ? Sort.Int() : context.univSort;
                namesToVars.put(name.label, var.of(varSort));

                if (declExpr == Sig.SIGINT) {
                    // Special case for the Int sig: don't bother translating the "var \in Int" condition
                    continue;
                }

                // Add the condition "var \in declExpr" to restrict the domain of var
                conditions.add(recursivelyTranslate(
                        ExprElementOf.make(var, declExpr), context));
            }
        }

        // All the conditions must be true for a set of variables to be used
        Term condition = conditions.isEmpty() ? Term.mkTop() : Term.mkAnd(conditions);
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
