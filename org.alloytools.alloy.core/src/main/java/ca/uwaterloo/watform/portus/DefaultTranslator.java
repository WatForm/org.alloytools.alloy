package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
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

    // For creating the scope axioms.
    private final ScopeAxiomStrategy scopeAxiomStrategy;

    // Membership predicates for each signature (see KT 4.2).
    // Represent it by a Java function taking "x" to "inA(x)".
    // (For some arguments the function might not just return inA(x) - it could return Top or Bottom as opts.)
    private final Map<Sig, Function<AnnotatedVar, Term>> sigMemberPredicates = new HashMap<>();

    // Relation predicates for each field (see KT 4.2).
    // Note: the function optimization is in FunctionOptTranslator instead.
    // Represent relations by a Java function taking "x1,...,xn" to "f(x1,...,xn)".
    // (Similarly, for some arguments the function might not return a call - it could return Top or Bottom as opts.)
    private final Map<Sig.Field, Function<VarTuple, Term>> relationPredicates = new HashMap<>();

    // Names of the above relation predicates for easy access.
    private final Map<Sig.Field, String> relationPredicateNames = new HashMap<>();

    // When "^expr" or "*expr" is translated, this "maps" expr and the auxiliary function's signature
    // to the name of an auxiliary function f_sort(x,y,extras) = [[(x,y,extras) \in expr]], used in the translation.
    // It's not a real map because Expr doesn't support equals()/hashCode() easily, and we can tolerate O(n) lookup.
    private final List<Pair<Pair<Expr, List<Sort>>, String>> auxClosureRelationNames = new ArrayList<>();

    public DefaultTranslator(Translator topLevelTranslator, ScopeAxiomStrategy scopeAxiomStrategy) {
        super(topLevelTranslator);
        this.scopeAxiomStrategy = scopeAxiomStrategy;
    }

    /** Translate a signature declaration. */
    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Internal error: seen sig " + sig.label + " before");
        }

        // Make a new predicate for membership, inSig: S -> Bool where S is sig's corresponding sort
        Sort sigSort = context.sortPolicy.getSort(sig);
        if (sigSort == null) {
            throw new ErrorFatal("Internal Portus error: signature " + sig + " cannot be assigned a sort");
        }
        String memPredName = context.nameGenerator.freshName("in" + sig.label);
        sigMemberPredicates.put(sig, var -> {
            // TODO: if sig is the entire sort, don't bother with the predicate and just return Top
            if (!var.sort().equals(sigSort)) {
                // Any other sort is not in the signature!
                return Term.mkBottom();
            }
            return Term.mkApp(memPredName, var.variable());
        });
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(memPredName, sigSort, Sort.Bool()));

        if (sig instanceof Sig.PrimSig) {
            Sig.PrimSig primSig = (Sig.PrimSig) sig;

            // Translate all its children so we can translate membership in them
            for (Sig.PrimSig child : primSig.children()) {
                recursivelyTranslate(child, context);
            }

            // Add axioms for membership
            for (Sig.PrimSig child : primSig.children()) {
                context.addAxiom(makeSubsetAxiom(Collections.singletonList(primSig), child, context));
            }

            // Add axioms for disjointness between each pair of subsigs
            for (int i = 0; i < primSig.children().size(); i++) {
                for (int j = i + 1; j < primSig.children().size(); j++) {
                    context.addAxiom(makeDisjointnessAxiom(
                            primSig.children().get(i), primSig.children().get(j), context));
                }
            }

            // Abstract sigs: add axiom that children cover sig
            if (sig.isAbstract != null) {
                context.addAxiom(makeCoverAxiom(primSig, context));
            }
        } else if (sig instanceof Sig.SubsetSig) {
            Sig.SubsetSig subsetSig = (Sig.SubsetSig) sig;

            // Assert the sig is a subset of its parents (or exactly its parents if exact)
            // Note: subsetSig.exact will be true iff it's declared like "sig C = A + B {}" (valid Alloy!)
            context.addAxiom(makeSubsetAxiom(subsetSig.parents, subsetSig, subsetSig.exact, context));
        } else {
            throw new ErrorFatal("Unsupported sig type!");
        }

        // Generate scope constraints
        int scope = context.scoper.sig2scope(sig);
        if (context.scoper.isExact(sig)) {
            context.addAxiom(scopeAxiomStrategy.makeExactScopeAxiom(sig, scope, topLevelTranslator, context));
        } else {
            context.addAxiom(scopeAxiomStrategy.makeNonExactScopeAxiom(sig, scope, topLevelTranslator, context));
        }

        // return Top because the returned Term doesn't matter for a Sig
        return Term.mkTop();
    }

    /** Create an axiom that child is a subset of the union of parents. If exact, declare it equal instead. */
    private Term makeSubsetAxiom(List<Sig> parents, Expr child, boolean exact, TranslationContext context) {
        // express in Alloy so we can translate to Fortress recursively
        // without assumptions on implementation of the translation
        // Alloy: "child in parent1 + parent2 + ... + parentn", no need to overcomplicate things
        // If exact, instead "child = parent1 + parent2 + ... + parentn"
        Expr union = parents.stream()
                .map(sig -> (Expr) sig) // annoying casting step necessary to satisfy the whims of Java generics
                .reduce(Expr::plus)
                .orElseThrow(() -> new ErrorFatal("Internal Portus error: subset axiom with no parents!"));
        Expr subsetAxiom = exact ? child.equal(union) : child.in(union);
        return recursivelyTranslate(subsetAxiom, context);
    }

    /** Default for convenience: not exact. */
    private Term makeSubsetAxiom(List<Sig> parents, Expr child, TranslationContext context) {
        return makeSubsetAxiom(parents, child, false, context);
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

    /** Translate "var \in sig". */
    @Override
    public Term translate(AnnotatedVar var, Sig sig, TranslationContext context) {
        // Special cases: builtin sigs
        if (sig.builtin) {
            if (sig.equals(Sig.UNIV)) {
                // "var \in univ" is always true
                return Term.mkTop();
            } else if (sig.equals(Sig.SIGINT)) {
                // it's an int iff its sort is int - evaluate at compile time using var's type
                return var.sort().equals(Sort.Int()) ? Term.mkTop() : Term.mkBottom();
            } else if (sig.equals(Sig.SEQIDX)) {
                // seq/Int is just ints in [0, maxseq-1] - TODO optimize sequences
                // Note: we use "<= maxseq - 1" and not "< maxseq" to support the case where
                // maxseq = 2^(bitwidth-1), so maxseq isn't representable in the bitwidth but maxseq-1 is.
                if (var.sort().equals(Sort.Int())) {
                    return Term.mkAnd(
                            Term.mkGE(var.variable(), IntegerLiteral.apply(0)),
                            Term.mkLE(var.variable(), IntegerLiteral.apply(context.getMaxSeq() - 1)));
                } else {
                    return Term.mkBottom();
                }
            } else if (sig.equals(Sig.STRING)) {
                // TODO - implement strings for real
                return Term.mkBottom();
            } else {
                throw new ErrorFatal("Unsupported builtin sig: " + sig);
            }
        }

        // If we recognize the sig, use its membership predicate
        if (!sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Unknown sig " + sig);
        }
        return sigMemberPredicates.get(sig).apply(var);
    }

    /** Translate a field declaration inside a sig. */
    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        // Find the Fortress sorts corresponding to the arguments of this field's predicate.
        List<Sort> argSorts = context.sortPolicy.getMinimalExprSorts(field,
                "A field declaration must have definite Portus sorts!", context);

        // Make a new predicate for the field relation (function optimization is elsewhere).
        String relName = context.nameGenerator.freshName(field.label);
        relationPredicates.put(field, vars -> {
            if (vars.size() != field.type().arity()) {
                throw new ErrorFatal("Field predicate arity mismatch: expected arity " + field.type().arity()
                        + " but got " + vars.size() + ".");
            }
            if (!vars.getSorts().equals(argSorts)) {
                // Sorts don't match, so it's definitely not in the field!
                return Term.mkBottom();
            }
            return Term.mkApp(relName, vars.getVars());
        });
        relationPredicateNames.put(field, relName);

        // the predicate signature is S1->S2->...->Sn->Bool, where Si is the ith product type's sort
        context.addFunctionDeclaration(FuncDecl.mkFuncDecl(relName, argSorts, Sort.Bool()));

        // constrain the bound of the field
        context.addAxiom(makeFieldBoundConstraint(field, argSorts, context));

        // just return Top because the returned term doesn't matter for a field declaration
        return Term.mkTop();
    }

    /** Create an axiom asserting that the field's relation stays within its bound. */
    private Term makeFieldBoundConstraint(Sig.Field field, List<Sort> argSorts, TranslationContext context) {
        // We translate the bound for "sig A { f: M e }" as [[all this: A | this.f in M e]] to constrain the range,
        // plus a domain constraint: forall x1:S1,...,xn:Sn . [[(x1,...,xn) \in f]] => [[x1 \in A]].
        // This is how Kodkod does it (effectively), and it elegantly handles "this" (generated as a variable when
        // fields refer to previously declared fields) as well as multiplicities (handled by "in").
        // TODO: this can be optimized for one sigs.
        // The sig.decl field is "this: sig".
        Expr thisVar = field.sig.decl.get();
        Expr rangeAxiomAlloy = thisVar.join(field).in(field.decl().expr).forAll(field.sig.decl);
        Term rangeAxiom = recursivelyTranslate(rangeAxiomAlloy, context);

        List<AnnotatedVar> vars = argSorts.stream()
                .map(sort -> Term.mkVar(context.nameGenerator.freshName("x")).of(sort))
                .collect(Collectors.toList());
        Term domainAxiom = Term.mkForall(vars, Term.mkImp(
                recursivelyTranslate(ExprElementOf.make(new VarTuple(vars), field), context),
                recursivelyTranslate(ExprElementOf.make(vars.get(0), field.sig), context)));

        return Term.mkAnd(domainAxiom, rangeAxiom);
    }

    @Override
    public Term translate(VarTuple tuple, Sig.Field field, TranslationContext context) {
        // if we recognize the field, use its relation
        if (!relationPredicates.containsKey(field)) {
            throw new ErrorFatal("Unknown field: " + field);
        }
        return relationPredicates.get(field).apply(tuple);
    }

    /** Translate "tuple \in expr", where expr is an ExprBinary term. */
    @Override
    public Term translate(VarTuple tuple, ExprBinary expr, TranslationContext context) {
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
                if (!tuple.getSort(0).equals(Sort.Int())) {
                    // Fortress will reject = with mismatched sorts, but we know they aren't equal if it's not an int
                    return Term.mkBottom();
                }
                return Term.mkEq(tuple.getVar(0), translateArithmeticOperation(
                        expr.op, expr.left, expr.right, context));
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprBinary term: " + expr.op);
        }
    }

    /** Translate "tuple \in left + right". */
    private Term translateUnion(VarTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkOr(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    /** Translate "tuple \in left & right". */
    private Term translateIntersection(VarTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    private Term translateSetDifference(VarTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                Term.mkNot(recursivelyTranslate(ExprElementOf.make(tuple, right), context)));
    }

    /** Translate "tuple \in left . right". */
    private Term translateJoin(VarTuple tuple, Expr left, Expr right, TranslationContext context) {
        // Naive join implementation without optimizations (see KT figure 4.11).
        // [[(x1,...,xn) \in e1 . e2]] := exists y: sort . [[(x1,...,xm,y) \in e1]] &&
        //   [[(y,x{m+1},...,xn) \in e2]] where arity(e1) = m+1 and arity(e2) = n-m+1 and m<n
        Var yVar = Term.mkVar(context.nameGenerator.freshName("y"));

        // What sort should y have?
        // Both the rightmost index in the left expression and the leftmost index in the right expression should
        // have compatible sorts: either both the same sort, or one should be indeterminate (null) according to
        // getMinimalExprSorts to signify it's compatible with both. (If both are null, we can't determine a sort.)
        int partitionIdx = left.type().arity() - 1; // so that adding y gives the arity
        String errorMsg = "Argument of join is ill-typed according to Portus sorts!";
        Sort leftYSort = context.sortPolicy.getMinimalExprSorts(left, errorMsg, context).get(partitionIdx);
        Sort rightYSort = context.sortPolicy.getMinimalExprSorts(right, errorMsg, context).get(0);
        Sort ySort;
        if (leftYSort == null) {
            ySort = rightYSort;
        } else if (rightYSort == null) {
            ySort = leftYSort;
        } else if (leftYSort != rightYSort) {
            throw new ErrorFatal("Joined column does not have consistent Fortress sort!");
        } else {
            ySort = leftYSort;
        }
        if (ySort == null) {
            // technical restriction: we need a definite sort for the exists variable
            throw new ErrorFatal("Joined column requires a definite Portus sort!");
        }
        AnnotatedVar y = yVar.of(ySort);

        // build up the tuples we'll recurse on
        // append y to make (x1, ..., xm, y)
        VarTuple leftSubTuple = tuple.slice(0, partitionIdx).concat(new VarTuple(y));
        // prepend y to make (y, x{m+1}, ..., xn)
        VarTuple rightSubTuple = new VarTuple(y).concat(tuple.slice(partitionIdx, tuple.size()));

        //noinspection SuspiciousNameCombination - IntelliJ is overzealous
        return Term.mkExists(y, Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(leftSubTuple, left), context),
                recursivelyTranslate(ExprElementOf.make(rightSubTuple, right), context)));
    }

    /** Translate "tuple \in left->right". */
    private Term translateCrossProduct(VarTuple tuple, Expr left, Expr right, TranslationContext context) {
        // [[(x1,...,xn) \in e1->e2]] := [[(x1,...,xm) \in e1]] && [[(x{m+1},...,xn) \in e2]]
        // where arity(e1) = m and arity(e2) = n-m
        if (left.type().arity() + right.type().arity() != tuple.size()) {
            throw new ErrorFatal("Cross product arities do not match!");
        }

        VarTuple leftSubTuple = tuple.slice(0, left.type().arity());
        VarTuple rightSubTuple = tuple.slice(left.type().arity(), tuple.size());
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(leftSubTuple, left), context),
                recursivelyTranslate(ExprElementOf.make(rightSubTuple, right), context));
    }

    /** Translate the formula "tuple \in domain <: expr". */
    private Term translateDomainRestriction(VarTuple tuple, Expr domain, Expr expr, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in domain <: expr]] := [[x1 \in domain]] && [[(x1,...,xn) \in expr]]
        // where arity(domain) = 1 and arity(expr) = n
        if (domain.type().arity() != 1) {
            throw new ErrorFatal("The left-hand side of a domain restriction must have arity 1.");
        }
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple.pick(0), domain), context),
                recursivelyTranslate(ExprElementOf.make(tuple, expr), context));
    }

    /** Translate the formula "tuple \in expr :> range". */
    private Term translateRangeRestriction(VarTuple tuple, Expr expr, Expr range, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in expr :> range]] := [[(x1,...,xn) \in expr]] && [[xn \in range]]
        // where arity(expr) = n and arity(range) = 1
        if (range.type().arity() != 1) {
            throw new ErrorFatal("The right-hand side of a range restriction must have arity 1.");
        }
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, expr), context),
                recursivelyTranslate(ExprElementOf.make(tuple.pick(tuple.size() - 1), range), context));
    }

    /** Translate the formula "tuple \in base ++ override". */
    private Term translateOverride(VarTuple tuple, Expr base, Expr override, TranslationContext context) {
        // KT figure 4.11: [[(x1,...,xn) \in base ++ override]] := [[(x1,...,xn) \in override]]
        // || ([[(x1,...,xn \in base]] && !(exists y2:S2,...,yn:Sn . [[(x1,y2,...,yn) \in override]]))
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

        // TODO: the *first* argument doesn't actually need a definite sort, can we not require it?
        List<Sort> overrideSorts = context.sortPolicy.getMinimalExprSorts(override,
                "The second argument to ++ must have definite Portus sorts!", context);

        // build up the vars x1,y2,...,yn and the annotated vars y2,...,yn
        List<AnnotatedVar> quantifiedVars = new ArrayList<>();
        List<AnnotatedVar> allVars = new ArrayList<>();
        allVars.add(tuple.getAnnotatedVar(0));
        for (int i = 1; i < arity; i++) {
            Var yVar = Term.mkVar(context.nameGenerator.freshName("y" + i));
            // TODO: how much short circuiting can we do here?
            AnnotatedVar y = yVar.of(overrideSorts.get(i));
            quantifiedVars.add(y);
            allVars.add(y);
        }

        // translate [[(x1,y2,...,yn) \in override]]
        Term firstInOverride = recursivelyTranslate(
                ExprElementOf.make(new VarTuple(allVars), override), context);

        return Term.mkOr(inOverride, Term.mkAnd(
                inBase, Term.mkNot(Term.mkExists(quantifiedVars, firstInOverride))));
    }

    /** Translate an ExprBinary formula or integer-valued expression. */
    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        if (PortusUtil.isDeclarationFormula(expr)) {
            return translateDeclarationFormula(expr.left, (ExprBinary) expr.right, context);
        }

        switch (expr.op) {
            // see KT figure 4.6
            case IMPLIES:
                context.sortPolicy.checkIsFormula("'=>' requires formulas on both sides", expr.left, expr.right);
                return Term.mkImp(
                        recursivelyTranslate(expr.left, context),
                        recursivelyTranslate(expr.right, context));
            case IFF:
                context.sortPolicy.checkIsFormula("'<=>' requires formulas on both sides", expr.left, expr.right);
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
            case JOIN:
                // "x.y" might be an integer expression, but we don't handle it here because it needs functions
                throw new ErrorFatal("Join integer expressions are only supported with the function optimization");
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
        // There might be optimization opportunities here for nested multiplicity arrows. TODO: some redundancies here
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
        // We also handle multiplicities on e2 in the case of "e1 in M e2", because Alloy supports formulas
        // like "a in ONEOF(b)" and these come up in translating field declarations.

        // Determine the sorts. We need to quantify over each term in each position, so we need a definite Portus sort
        // for each position, but we also need to support constructions like "f in iden", so we can't demand that both
        // e1 and e2 have definite sorts in the 'in' case (since iden's sorts are indefinite).
        // We strike the following compromise:
        // - in "e1 = e2", e1 and e2 must have equal definite sorts. This disallows tricky cases like "f = iden".
        // - in "e1 in e2", e1 must have definite sorts which are subsets of the (definite or indefinite) sorts of e2.
        //   We will quantify over e1's sorts. This disallows "iden in f" but allows "f in iden", which is common.
        // Currently we reject formulas that don't meet these standards, but there's room for short-circuiting.
        String sortErrMsg = "Both sides in an 'in' or '=' formula must have well-defined Portus sorts!";
        List<Sort> e1Sorts = context.sortPolicy.getMinimalExprSorts(e1, sortErrMsg, context);
        List<Sort> e2Sorts = context.sortPolicy.getMinimalExprSorts(e2, sortErrMsg, context);
        assert e1Sorts.size() == e2Sorts.size(); // typechecker should have ensured this
        List<Sort> sorts = new ArrayList<>();
        for (int i = 0; i < e1Sorts.size(); i++) {
            // Merge the sorts as described above.
            Sort e1Sort = e1Sorts.get(i), e2Sort = e2Sorts.get(i);
            if (op == ExprBinary.Op.EQUALS) {
                // they must be equal definite sorts: disallow "f = iden"
                boolean ok = (e1Sort == e2Sort && SortPolicy.isSortDefinite(e1Sort));
                if (!ok) {
                    // TODO: can we short-circuit here? Requires knowing whether there are other sorts
                    throw new ErrorFatal("Both sides of an '=' formula must have the same definite Portus sorts.");
                }
            } else { // ExprBinary.Op.IN
                // in "e1 in e2", e1 must have definite sorts that are a subset of e2's sorts
                // so we allow "f in iden", but not "iden in f"
                boolean ok = (SortPolicy.isSortDefinite(e1Sort) && SortPolicy.isSortSubset(e1Sort, e2Sort));
                if (!ok) {
                    // TODO: short-circuiting here as well?
                    throw new ErrorFatal("The left side of an 'in' must have definite Portus sorts that are a" +
                            " subset of the right side's sorts.");
                }
            }
            // Use the left side's sorts in either case (they'll be equal if it's an '=' formula).
            sorts.add(e1Sort);
        }

        // Create the variables
        // TODO: also think about how much short circuiting we can do here
        List<AnnotatedVar> vars = IntStream.range(0, e1.type().arity())
                .mapToObj(idx -> Term.mkVar(context.nameGenerator.freshName("x" + idx))
                        .of(sorts.get(idx)))
                .collect(Collectors.toList());

        Term inE1 = recursivelyTranslate(ExprElementOf.make(new VarTuple(vars), e1), context);
        Term inE2 = recursivelyTranslate(ExprElementOf.make(new VarTuple(vars), e2), context);
        Term condition;
        Expr multCondition = null;
        if (op == ExprBinary.Op.EQUALS || e2.mult() == ExprUnary.Op.EXACTLYOF) {
            // "exactly" is used in the meta feature and means to treat "in exactly" like "=" as a hack
            condition = Term.mkIff(inE1, inE2);
        } else { // ExprBinary.Op.IN
            condition = Term.mkImp(inE1, inE2);

            // Add additional "M e2" conditions for "e1 in M e2", where M is a multiplicity
            switch (e2.mult()) {
                case ONEOF:
                    multCondition = e2.one();
                    break;
                case LONEOF:
                    multCondition = e2.lone();
                    break;
                case SOMEOF:
                    multCondition = e2.some();
                    break;
            }
        }

        Term result = Term.mkForall(vars, condition);
        if (multCondition != null) {
            result = Term.mkAnd(result, recursivelyTranslate(multCondition, context));
        }
        return result;
    }

    /** Translate "lhs op rhs", where op is an arithmetic comparison like <, >, =<, >=.  */
    private Term translateArithmeticComparison(ExprBinary.Op op, Expr lhs, Expr rhs, TranslationContext context) {
        context.sortPolicy.checkIsInt(op + " requires both sides to be integers!", lhs, rhs);

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
        context.sortPolicy.checkIsInt(op + " requires both sides to be integer expressions!", lhs, rhs);

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

    /** Translate the formula (or int expression) "f1 => f2 else f3". */
    @Override
    public Term translate(ExprITE expr, TranslationContext context) {
        // use Fortress's built-in if-then-else
        context.sortPolicy.checkIsFormula("The condition of if-then-else must be a formula!", expr.cond);
        Term cond = recursivelyTranslate(expr.cond, context);
        Term left = recursivelyTranslate(expr.left, context);
        Term right = recursivelyTranslate(expr.right, context);
        return Term.mkIfThenElse(cond, left, right);
    }

    /** Translate the formula "tuple \in (f => e1 else e2)". */
    @Override
    public Term translate(VarTuple tuple, ExprITE expr, TranslationContext context) {
        // Similar to the above: "IfThenElse([[f]], [[tuple \in e1]], [[tuple \in e2]])"
        context.sortPolicy.checkIsFormula("The condition of if-then-else must be a formula!", expr.cond);
        Term cond = recursivelyTranslate(expr.cond, context);
        Term left = recursivelyTranslate(ExprElementOf.make(tuple, expr.left), context);
        Term right = recursivelyTranslate(ExprElementOf.make(tuple, expr.right), context);
        return Term.mkIfThenElse(cond, left, right);
    }

    /** Translate an ExprUnary formula (or int expression). */
    @Override
    public Term translate(ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOT:
                // see KT figure 4.6
                context.sortPolicy.checkIsFormula("The argument of '!' must be a formula!", expr.sub);
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
            // These are markers for use in field declarations/in expressions, ignore them translating this expr.
            case ONEOF:
            case SOMEOF:
            case LONEOF:
            case EXACTLYOF:
            case SETOF:
            // These appear to be for internal use in the Alloy->Kodkod translation, ignore for now.
            case CAST2INT:
            case CAST2SIGINT:
                return recursivelyTranslate(expr.sub, context);
            case CARDINALITY:
                return translateCardinality(expr.sub, context);
            default:
                // others are either not supported or not formulas
                throw new ErrorFatal("Unsupported ExprUnary formula: " + expr.op);
        }
    }

    /** Translate "#e", as an integer expression. */
    private Term translateCardinality(Expr expr, TranslationContext context) {
        // Equivalent to "sum x1:S1,...,xn:Sn | ((x1,...,xn) \in e) => 1 else 0" where n = arity(e),
        // so translate as such for simplicity. Use translateSum() directly instead of recursively translating because
        // to translate the Alloy above directly, we'd need to augment ExprElementOf to allow taking ExprVars and
        // delaying their evaluation into Fortress Vars until we're within the sum's scope and x1,...,xn are bound.
        List<AnnotatedVar> vars = new ArrayList<>();
        List<Sort> sorts = context.sortPolicy.getMinimalExprSorts(expr, "", context);
        for (int i = 0; i < expr.type().arity(); i++) {
            Var var = Term.mkVar("x" + i);
            vars.add(var.of(sorts.get(i)));
        }

        Term condition = recursivelyTranslate(ExprElementOf.make(new VarTuple(vars), expr), context);
        return translateSum(IntegerLiteral.apply(1), condition, vars, context);
    }

    /** Translate "tuple \in expr", where expr is an ExprUnary formula. */
    @Override
    public Term translate(VarTuple tuple, ExprUnary expr, TranslationContext context) {
        switch (expr.op) {
            case NOOP:
                // no-op: ignore it
                return recursivelyTranslate(ExprElementOf.make(tuple, expr.deNOP()), context);
            case TRANSPOSE:
                return translateTranspose(tuple, expr.sub, context);
            case CARDINALITY:
                return translateInIntExpr(tuple, expr, context);
            case CLOSURE:
                return translateClosure(false, tuple, expr.sub, context);
            case RCLOSURE:
                return translateClosure(true, tuple, expr.sub, context);
            // These are markers for use in field declarations/in expressions, ignore them translating this expr.
            case ONEOF:
            case SOMEOF:
            case LONEOF:
            case EXACTLYOF:
            case SETOF:
            // These appear to be for internal use in the Alloy->Kodkod translation, ignore for now.
            case CAST2INT:
            case CAST2SIGINT:
                return recursivelyTranslate(ExprElementOf.make(tuple, expr.sub), context);
            default:
                // others are either not supported or not terms
                throw new ErrorFatal("Unsupported ExprUnary term: " + expr.op);
        }
    }

    /** Translate "tuple \in ~sub". */
    private Term translateTranspose(VarTuple tuple, Expr sub, TranslationContext context) {
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Transpose argument must have arity 2");
        }

        // swap the variables in the tuple - see KT figure 4.11
        VarTuple swapped = tuple.pick(1).concat(tuple.pick(0));
        return recursivelyTranslate(ExprElementOf.make(swapped, sub), context);
    }

    /** Translate "tuple \in ^sub" (reflexive==false) or "tuple \in *sub" (reflexive==true). */
    private Term translateClosure(boolean reflexive, VarTuple tuple, Expr sub, TranslationContext context) {
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Closure argument must have arity 2");
        }

        // If the sorts aren't the same, we can't translate.
        // (We can't short-circuit: consider (a,b) \in ^iden vs (a,b) \in ^(univ->univ) where a,b have different sorts)
        if (!tuple.getSort(0).equals(tuple.getSort(1))) {
            throw new ErrorFatal("Portus doesn't support transitive closure with distinct Fortress sorts!");
        }
        Sort commonSort = tuple.getSort(0);

        // Translate as "^f(x,y)" or "*f(x,y)" where f is an auxiliary relation f(x,y) = [[(x,y) \in sub]].
        // Also include all the free variables as secondary arguments.
        String auxRelationName = makeClosureBinaryRelation(commonSort, sub, context);
        List<Term> freeVars = PortusUtil.computeFreeVariables(sub, context).stream()
                .map(AnnotatedVar::variable)
                .collect(Collectors.toList());
        if (reflexive) {
            return Term.mkReflexiveClosure(auxRelationName, tuple.getVar(0), tuple.getVar(1), freeVars);
        } else {
            return Term.mkClosure(auxRelationName, tuple.getVar(0), tuple.getVar(1), freeVars);
        }
    }

    // Fortress can only take the closure of a binary relation and not an arbitrary expression, so find a
    // convenient relation to take the closure of for taking the closure of expr and return its name.
    // `sort` is the sort of the arguments, expr must have a compatible type with `sort->sort`.
    // We use a new auxiliary function for each sort so things like "^iden" work correctly.
    private String makeClosureBinaryRelation(Sort sort, Expr expr, TranslationContext context) {
        expr = expr.deNOP(); // Eliminate any no-ops which could mess up our optimizations

        // Does expr happen to already be a binary relation (field of arity 2)? If so, just use it.
        if (expr instanceof Sig.Field) {
            Sig.Field field = (Sig.Field) expr;
            // It's possible that the function optimization optimized this field, so we don't have it.
            // TODO: is it possible to close over a binary function in the function optimization?
            if (field.type().arity() == 2 && relationPredicateNames.containsKey(field)) {
                return relationPredicateNames.get(field);
            }
        }

        // The type of the aux relation is (sort,sort,*extras)->Bool
        List<AnnotatedVar> freeVars = PortusUtil.computeFreeVariables(expr, context);
        List<Sort> auxRelSorts = new ArrayList<>();
        auxRelSorts.add(sort);
        auxRelSorts.add(sort);
        auxRelSorts.addAll(freeVars.stream().map(AnnotatedVar::sort).collect(Collectors.toList()));

        // Have we already translated this expr/sort combo? If so, use its name.
        for (Pair<Pair<Expr, List<Sort>>, String> exprAndClosureName : auxClosureRelationNames) {
            Expr prevExpr = exprAndClosureName.a.a;
            List<Sort> prevSorts = exprAndClosureName.a.b;
            if (auxRelSorts.equals(prevSorts) && expr.isSame(prevExpr)) {
                return exprAndClosureName.b;
            }
        }

        if (!expr.type().hasArity(2)) {
            throw new ErrorSyntax("We can only take the transitive/reflexive closure of binary expressions.");
        }

        // Introduce an auxiliary relation f(x,y) = [[(x,y) \in expr]] of type sort->sort
        // Also include any free variables in the term as extra arguments.
        String auxRelationName = context.nameGenerator.freshName("closureAux_" + sort.name());
        auxClosureRelationNames.add(new Pair<>(new Pair<>(expr, auxRelSorts), auxRelationName));
        FuncDecl auxDecl = FuncDecl.mkFuncDecl(auxRelationName, auxRelSorts, Sort.Bool());
        context.addFunctionDeclaration(auxDecl);

        // Give it our desired interpretation with an axiom "forall x, y: sort . f(x,y) = [[(x, y) \in expr]]".
        // TODO: this can be done more cheaply (avoiding the forall) with a definition instead
        Var x = Term.mkVar(context.nameGenerator.freshName("x"));
        Var y = Term.mkVar(context.nameGenerator.freshName("y"));
        List<AnnotatedVar> axiomDecls = new ArrayList<>(Arrays.asList(x.of(sort), y.of(sort)));
        axiomDecls.addAll(freeVars);
        List<Var> allVars = axiomDecls.stream().map(AnnotatedVar::variable).collect(Collectors.toList());
        Term inExpr = recursivelyTranslate(ExprElementOf.make(
                new VarTuple(x.of(sort), y.of(sort)), expr), context);
        context.addAxiom(Term.mkForall(axiomDecls,
                Term.mkIff(
                        Term.mkApp(auxRelationName, allVars),
                        inExpr)));

        return auxRelationName;
    }

    /** Translate an ExprList formula. */
    @Override
    public Term translate(ExprList expr, TranslationContext context) {
        if (expr.op == ExprList.Op.DISJOINT) {
            return translateDisjoint(expr.args, context);
        } else if (expr.op == ExprList.Op.TOTALORDER) {
            throw new ErrorFatal("Portus does not yet support TOTALORDER");
        }

        // first, just translate all the args (they all must be formulas)
        context.sortPolicy.checkIsFormula("AND or OR arguments must all be formulas", expr.args);
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

    /** Translate "disj [e1,...,en]", asserting that e1,...,en are all disjoint. */
    private Term translateDisjoint(List<Expr> args, TranslationContext context) {
        // If there's <=1 argument, short-circuit to true (doesn't make much sense)
        if (args.size() <= 1) {
            return Term.mkTop();
        }

        // The common case is that e1,...,en are all bound vars, which comes from desugaring "all disj"/"no disj"/etc.
        // If this is the case (or, in theory, e1,...,en are otherwise all convertible to Fortress Terms), then we can
        // directly use Fortress's "distinct" primitive.
        // In theory e1,...,en can be arbitrary expressions, but the "disj [e1,...,en]" construct is poorly
        // documented and probably not well-used, so we don't support it for now. We only support bound vars.
        List<AnnotatedVar> vars = args.stream().map(arg -> {
            if (arg instanceof ExprVar) {
                ExprVar var = (ExprVar) arg;
                if (context.hasVarMapping(var.label)) {
                    return context.getVarMapping(var.label);
                }
            }
            throw new ErrorFatal("Portus only supports disj[] with bound variables.");
        }).collect(Collectors.toList());

        // Make sure they have the same sort - we don't support it if they don't.
        // (If we do have to support this - partition by sort and map to a conjunction of distincts.)
        if (vars.stream().map(AnnotatedVar::sort).distinct().count() > 1) {
            throw new ErrorFatal("Portus only supports disj[] with variables of the same top-level sort.");
        }

        return Term.mkDistinct(vars.stream().map(AnnotatedVar::variable).collect(Collectors.toList()));
    }

    /** Translate "Q e", where Q is one of {one, lone, some, no} and e is an expression. */
    private Term translateQuantifiedExpr(ExprQt.Op quantifier, Expr expr, TranslationContext context) {
        // "Q e" is equivalent to "Q x1:S1,...,xn:Sn | (x1,...,xn) \in e" where n = arity(e), so translate as such
        // for simplicity.
        int arity = expr.type().arity();
        if (arity <= 0) {
            throw new ErrorFatal("Portus doesn't support types with multiple arities");
        }
        List<AnnotatedVar> vars = new ArrayList<>(arity);

        List<Sort> exprSorts = context.sortPolicy.getMinimalExprSorts(expr,
                "Translating a quantified expression requires the inner expression to have well-defined sorts!",
                context);
        SortPolicy.requireAllSortsDefinite(exprSorts,
                "Translating a quantified expression requires the inner expression's sorts to all be definite!");
        for (int i = 0; i < arity; i++) {
            Var var = Term.mkVar(context.nameGenerator.freshName("x" + i));
            vars.add(var.of(exprSorts.get(i)));
        }

        // technically, we actually translate as pseudo-Alloy "Q (x1,...,xn): e | true", so there's an extra true
        Term condition = recursivelyTranslate(ExprElementOf.make(new VarTuple(vars), expr), context);
        Term sub = Term.mkTop();
        return translateRawQuantifier(quantifier, vars, condition, sub, context);
    }

    /** Translate an ExprQt formula. */
    @Override
    public Term translate(ExprQt expr, TranslationContext context) {
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
        Term sub;
        try {
            sub = recursivelyTranslate(expr.sub, context);
        } finally {
            // Remove the vars from the lexical scope since it's done (always, even if there's an exception)
            for (String alloyVarName : namesToVars.keySet()) {
                context.removeMapping(alloyVarName);
            }
        }

        return translateRawQuantifier(expr.op, vars, condition, sub, context);
    }

    /** Translate "Q vars: e | f" after the vars, condition (vars \in e) and the subformula have been translated. */
    private Term translateRawQuantifier(
            ExprQt.Op quantifier, List<AnnotatedVar> vars, Term condition, Term sub, TranslationContext context) {
        // Process the formula itself - see KT figure 4.6
        if (quantifier == ExprQt.Op.NO) {
            // "no x: e | f" gets translated like "all x: e | not f"
            return translateRawQuantifier(ExprQt.Op.ALL, vars, condition, Term.mkNot(sub), context);
        }
        switch (quantifier) {
            case ALL:
                // forall x1: S, ..., xn: S . [[x1 \in e1]] && ... && [[xn \in en]] => [[sub]]
                return Term.mkForall(vars, Term.mkImp(condition, sub));
            case SOME:
                // exists x1: S, ..., xn: S . [[x1 \in e1]] && ... && [[xn \in en]] && [[sub]]
                return Term.mkExists(vars, Term.mkAnd(condition, sub));
            case LONE: {
                // naive for now
                // forall x, y: S . [[x \in e]] && [[y \in e]] && [[f]] && [[f[x/y]]] => x = y
                List<AnnotatedVar> primed = prime(vars, context);
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
                List<AnnotatedVar> primed = prime(vars, context);
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
                throw new ErrorFatal("Unsupported quantifier: " + quantifier);
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
            Sort sort = var.sort();
            sorts.add(sort);
            // Note: this is OK for Int because getSortScope(Sort.Int()) returns the number of ints, not the bitwidth
            sortScopes.add(context.sortPolicy.getSortScope(sort));
            currentIdxs.add(1);

            // We're expanding over the domain elements of the sort, so its scope can't be changed arbitrarily
            // in the output - mark it unchanging
            context.markSortUnchanging(sort);
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
    public Term translate(VarTuple tuple, ExprQt expr, TranslationContext context) {
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
    private Term translateComprehension(VarTuple tuple, ExprQt expr, TranslationContext context) {
        // [[(x1,...,xn) \in {y1: e1, ..., yn: en | f(y1,...,yn)}]] :=
        // [[x1 \in e1]] && ... && [[xn \in en]] && [[f(y1,...,yn)]] where yi is mapped to xi
        // First, check the arity is correct
        if (tuple.size() != expr.count()) {
            throw new ErrorSyntax("Mismatched arity for comprehension expression!");
        }

        // Pair the vars and decls/names
        List<Pair<AnnotatedVar, Pair<Decl, ExprHasName>>> varsAndDecls = new ArrayList<>();
        int tupleIdx = 0;
        for (Decl decl : expr.decls) {
            for (ExprHasName name : decl.names) {
                AnnotatedVar var = tuple.getAnnotatedVar(tupleIdx);
                varsAndDecls.add(new Pair<>(var, new Pair<>(decl, name)));
                tupleIdx++;
            }
        }

        List<Term> conjuncts = new ArrayList<>();

        // Generate each [[xi \in ei]] conjunct
        for (Pair<AnnotatedVar, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
            AnnotatedVar var = varAndDecl.a;
            Decl decl = varAndDecl.b.a;
            // Unwrap the expression from its multiplicity (and any NOOPs)
            Expr declExpr = decl.expr.deNOP();
            if (declExpr.mult == 1) {
                // We know this is an ExprUnary because decl.expr.mult() must return ONEOF,
                // because ExprQt doesn't allow comprehension decls to have other multiplicities.
                ExprUnary wrappedDeclExpr = (ExprUnary) declExpr;
                declExpr = wrappedDeclExpr.sub;
            }
            Expr conjunct = ExprElementOf.make(new VarTuple(var), declExpr);
            conjuncts.add(recursivelyTranslate(conjunct, context));
        }

        // Map each yi to xi - do this after generating conjuncts to avoid any interference
        for (Pair<AnnotatedVar, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
            AnnotatedVar var = varAndDecl.a;
            ExprHasName name = varAndDecl.b.b;
            context.addVarMapping(name.label, var);
        }

        // Map [[f(y1,...,yn)]]
        try {
            conjuncts.add(recursivelyTranslate(expr.sub, context));
        } finally {
            // Unmap all the yi's (and do it even if there's an exception)
            for (Pair<AnnotatedVar, Pair<Decl, ExprHasName>> varAndDecl : varsAndDecls) {
                ExprHasName name = varAndDecl.b.b;
                context.removeMapping(name.label);
            }
        }

        return Term.mkAnd(conjuncts);
    }

    /** Translate an ExprLet formula. */
    @Override
    public Term translate(ExprLet let, TranslationContext context) {
        // Bind the variable in the context, translate the subformula, and remove the variable.
        context.addLetMapping(let.var.label, let.expr);
        Term result;
        try {
            result = recursivelyTranslate(let.sub, context);
        } finally { // ensure we always remove the mapping even if there's an exception
            context.removeMapping(let.var.label);
        }
        return result;
    }

    /** Translate "tuple \in expr", where expr is an ExprLet. */
    @Override
    public Term translate(VarTuple tuple, ExprLet let, TranslationContext context) {
        // Like above: bind the variable, translate "tuple \in let.sub", and remove the variable.
        context.addLetMapping(let.var.label, let.expr);
        Term result;
        try {
            result = recursivelyTranslate(ExprElementOf.make(tuple, let.sub), context);
        } finally { // always remove even if there's an exception
            context.removeMapping(let.var.label);
        }
        return result;
    }

    /** Translate "tuple \in expr", where expr is an ExprVar. */
    @Override
    public Term translate(VarTuple tuple, ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            TranslationContext.LetContext letContext = context.getLetMapping(expr.label);
            assert letContext != null;

            // Ensure we use the variable mappings from the let expression's location;
            // this avoids e.g. infinite recursion on "let a = a"
            letContext.useLetMapping(context);
            try {
                Expr mapped = ExprElementOf.make(tuple, letContext.getExpr());
                return recursivelyTranslate(mapped, context);
            } finally {
                letContext.resetMapping();
            }
        }

        // KT figure 4.12: [[x \in v]] := x = v
        if (tuple.size() != 1) {
            throw new ErrorFatal("Wrong arity for ExprVar!");
        }
        AnnotatedVar mapped = checkAndMapVarName(expr.label, context);
        // If the sorts are mismatched, short-circuit (the tuple can't be in the expr)
        if (!tuple.getSort(0).equals(mapped.sort())) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getVar(0), mapped.variable());
    }

    /** Translate an ExprVar integer expression. */
    @Override
    public Term translate(ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            TranslationContext.LetContext letContext = context.getLetMapping(expr.label);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return recursivelyTranslate(letContext.getExpr(), context);
            } finally {
                letContext.resetMapping();
            }
        }
        return checkAndMapVarName(expr.label, context).variable();
    }

    /** Translate an ExprConstant formula/integer expression. */
    @Override
    public Term translate(ExprConstant expr, TranslationContext context) {
        // The only ExprConstant formulas are TRUE and FALSE - we generate them in recursive translations.
        // Also translate numbers (and min/max) since they're integer expressions (standalone).
        switch (expr.op) {
            case TRUE:
                return Term.mkTop();
            case FALSE:
                return Term.mkBottom();
            case NUMBER:
                return IntegerLiteral.apply(expr.num);
            case MIN:
                return IntegerLiteral.apply(Util.min(context.getBitwidth()));
            case MAX:
                return IntegerLiteral.apply(Util.max(context.getBitwidth()));
            default:
                throw new ErrorFatal("Unsupported ExprConstant formula/int expression: " + expr);
        }
    }

    /** Translate "tuple \in expr", where expr is an ExprConstant. */
    @Override
    public Term translate(VarTuple tuple, ExprConstant expr, TranslationContext context) {
        switch (expr.op) {
            case IDEN:
                return translateIden(tuple);
            case EMPTYNESS:
                // "tuple \in none" is always false
                return Term.mkBottom();
            case NUMBER:
            case MIN:
            case MAX:
                return translateInIntExpr(tuple, expr, context);
            case NEXT:
                return translateNext(tuple, context);
            default:
                throw new ErrorFatal("Unsupported ExprConstant expression: " + expr);
        }
    }

    /** Translate "tuple \in iden". */
    private Term translateIden(VarTuple tuple) {
        // KT figure 4.12: [[(x1, x2) \in iden]] := x1 = x2
        // note that this works even for incompatible top-level sigs since we use a universal sort
        if (tuple.size() != 2) {
            throw new ErrorFatal("iden expects arity 2, but got " + tuple.size());
        }
        // if the sorts are different, then they can't be equal: short-circuit
        if (!tuple.getSort(0).equals(tuple.getSort(1))) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getVar(0), tuple.getVar(1));
    }

    /** Translate "tuple \in next". */
    private Term translateNext(VarTuple tuple, TranslationContext context) {
        // Translate as [[(x1, x2) \in next]] := x1 != max && x1 + 1 = x2
        // Alloy semantics dictate that "max . next = none", so we add a guard.
        // In fact, even with "prevent overflow" enabled, Alloy has "max.next = none" (even when max + 1 = min)!
        // So we add this guard to comply with the (rather inconsistent) semantics for next.
        if (tuple.size() != 2) {
            throw new ErrorFatal("integer/next expects arity 2, but got " + tuple.size());
        }
        if (tuple.getSort(0) != Sort.Int() || tuple.getSort(1) != Sort.Int()) {
            // next is Int->Int, so short-circuit here (typechecking should catch this)
            return Term.mkBottom();
        }
        int max = Util.max(context.getBitwidth());
        Term guard = Term.mkNot(Term.mkEq(tuple.getVar(0), IntegerLiteral.apply(max)));
        Term check = Term.mkEq(Term.mkPlus(tuple.getVar(0), IntegerLiteral.apply(1)), tuple.getVar(1));
        return Term.mkAnd(guard, check);
    }

    /** Translate a predicate or integer-valued function call. */
    @Override
    public Term translate(ExprCall call, TranslationContext context) {
        return translateCall(call.fun.getBody(), call, context);
    }

    /** Translate "tuple \in call", where call is a function call. */
    @Override
    public Term translate(VarTuple tuple, ExprCall call, TranslationContext context) {
        return translateCall(ExprElementOf.make(tuple, call.fun.getBody()), call, context);
    }

    /** Translate a pred or fun, but where "body" is the expr to recursively translate in scope. */
    private Term translateCall(Expr body, ExprCall call, TranslationContext context) {
        // Just naively substitute it.
        // TODO: handle recursion - currently we loop forever
        if (call.args.size() != call.fun.count()) {
            throw new ErrorFatal("Wrong number of arguments to predicate or function!");
        }

        context.addLetMappingsFromCall(call);

        Term result;
        try {
            result = recursivelyTranslate(body, context);
        } finally {
            // Remove the let mappings even if there's an exception
            context.removeLetMappingsFromCall(call);
        }

        return result;
    }

    private Term translateInIntExpr(VarTuple tuple, Expr intExpr, TranslationContext context) {
        if (tuple.size() != 1) {
            throw new ErrorSyntax("Int expression '" + intExpr + "' requires arity 1");
        }
        // assume intExpr is really an integer expression, and short-circuit if tuple isn't of type Int
        if (!tuple.getSort(0).equals(Sort.Int())) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getVar(0), recursivelyTranslate(intExpr, context));
    }

    /** Map an Alloy variable name to a Fortress term, or throw an error. */
    private AnnotatedVar checkAndMapVarName(String label, TranslationContext context) {
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
                ExprUnary.Op mult = decl.expr.mult();
                if (mult != ExprUnary.Op.ONEOF) {
                    // Treat "no multiplicity" as ONEOF because Alloy sometimes generates those internally.
                    // mult() generates SETOF for no multiplicity, so check that either the expr isn't actually
                    // an ExprUnary or it's an ExprUnary with a different op.
                    boolean noMultiplicity = mult == ExprUnary.Op.SETOF
                            && (!(decl.expr.deNOP() instanceof ExprUnary)
                                || ((ExprUnary) decl.expr.deNOP()).op != ExprUnary.Op.SETOF);
                    if (!noMultiplicity) {
                        throw new ErrorFatal("Unsupported quantifier multiplicity for Fortress: "
                                + decl.expr.mult());
                    }
                }

                // Unwrap the expression from its multiplicity (and any NOOPs)
                Expr declExpr = decl.expr.deNOP();
                if (declExpr instanceof ExprUnary) {
                    ExprUnary wrappedDeclExpr = (ExprUnary) decl.expr.deNOP();
                    if (wrappedDeclExpr.op == ExprUnary.Op.ONEOF) {
                        declExpr = wrappedDeclExpr.sub.deNOP();
                    }
                }

                Var var = Term.mkVar(context.nameGenerator.freshName(name.label));
                // Note that the decl expr has to be unary since typechecking should have caught anything else
                String definiteSortsError = "Translating a quantification requires the variable declarations " +
                        "to have definite and well-defined Portus sorts!";
                List<Sort> exprSorts = context.sortPolicy.getMinimalExprSorts(declExpr, definiteSortsError, context);
                if (exprSorts.size() != 1) {
                    // Could happen for cases Kodkod skolemizes, like e.g. "some s: one A->B | ..."
                    // Also occurs e.g. with "pred foo[s: A->B] {...}; run foo" since that runs "some s: A->B | foo[s]"
                    throw new ErrorFatal("Portus doesn't support quantifying over tuples!");
                }
                SortPolicy.requireAllSortsDefinite(exprSorts, definiteSortsError);
                Sort varSort = exprSorts.get(0);
                AnnotatedVar annotatedVar = var.of(varSort);
                namesToVars.put(name.label, annotatedVar);

                // Add it to the lexical scope to translate the condition and subformula
                context.addVarMapping(name.label, annotatedVar);

                // Add the condition "var \in declExpr" to restrict the domain of var
                conditions.add(recursivelyTranslate(
                        ExprElementOf.make(new VarTuple(annotatedVar), declExpr), context));
            }
        }

        // All the conditions must be true for a set of variables to be used
        Term condition = conditions.isEmpty() ? Term.mkTop() : Term.mkAnd(conditions);
        return new Pair<>(namesToVars, condition);
    }

    /** Generate a copy of `vars` with each variable suffixed with "_prime". */
    private List<AnnotatedVar> prime(List<AnnotatedVar> vars, TranslationContext context) {
        return vars.stream()
                .map(var -> Term.mkVar(context.nameGenerator.freshName(var.variable().name() + "_prime"))
                        .of(var.sort()))
                .collect(Collectors.toList());
    }

}
