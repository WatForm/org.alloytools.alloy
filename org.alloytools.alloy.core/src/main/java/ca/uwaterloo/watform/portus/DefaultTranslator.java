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
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * The basic translator that provides unoptimized translations of every supported node.
 */
final class DefaultTranslator extends AbstractTranslator implements Evaluator, ScopeExpansionMarker {

    // For creating the scope axioms.
    private final ScopeAxiomStrategy scopeAxiomStrategy;

    // For creating the other sig axioms.
    private final SigAxioms sigAxioms;

    // For determining sorts.
    private final SortPolicy sortPolicy;

    // For generating unique names for things.
    private final NameGenerator nameGenerator;

    // Membership predicates for each signature (see KT 4.2).
    // Represent it by a Java function taking "x" to "inA(x)".
    // (For some arguments the function might not just return inA(x) - it could return Top or Bottom as opts.)
    private final Map<Sig, Function<AnnotatedTerm, Term>> sigMemberPredicates = new HashMap<>();

    // Names of the above sig member predicates for easy access.
    private final Map<Sig, FuncDecl> sigMemberPredicateDecls = new HashMap<>();

    // Relation predicates for each field (see KT 4.2).
    // Note: the function optimization is in FunctionOptTranslator instead.
    // Represent relations by a Java function taking "x1,...,xn" to "f(x1,...,xn)".
    // (Similarly, for some arguments the function might not return a call - it could return Top or Bottom as opts.)
    private final Map<Sig.Field, Function<TermTuple, Term>> relationPredicates = new HashMap<>();

    // Names of the above relation predicates for easy access.
    private final Map<Sig.Field, FuncDecl> relationPredicateDecls = new HashMap<>();

    // When "^expr" or "*expr" is translated, this maps expr and the auxiliary function's signature
    // to the name of an auxiliary function f_sort(x,y,extras) = [[(x,y,extras) \in expr]], used in the translation.
    private final ExprCache<String> auxClosureRelationNames;

    public DefaultTranslator(
            Translator topLevelTranslator, ScopeAxiomStrategy scopeAxiomStrategy, SigAxioms sigAxioms,
            SortPolicy sortPolicy, NameGenerator nameGenerator) {
        super(topLevelTranslator);
        this.scopeAxiomStrategy = scopeAxiomStrategy;
        this.sigAxioms = sigAxioms;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.auxClosureRelationNames = new ExprCache<>(sortPolicy);
    }

    @Override
    public String name() {
        return "Default";
    }

    /** Translate a signature declaration. */
    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Internal error: seen sig " + sig.label + " before");
        }

        // Make a new predicate for membership, inSig: S -> Bool where S is sig's corresponding sort
        Sort sigSort = sortPolicy.getSort(sig);
        if (sigSort == null) {
            throw new ErrorFatal("Internal Portus error: signature " + sig + " cannot be assigned a sort");
        }
        String memPredName = nameGenerator.freshName("in" + sig.label);
        sigMemberPredicates.put(sig, term -> {
            if (!term.getSort().equals(sigSort)) {
                // Any other sort is not in the signature!
                return Term.mkBottom();
            }
            return Term.mkApp(memPredName, term.getTerm());
        });

        // Generate the membership predicate.
        // Note: we always do this here, optimizing it out is handled by MembershipPredicateOptTranslator
        FuncDecl decl = FuncDecl.mkFuncDecl(memPredName, sigSort, Sort.Bool());
        sigMemberPredicateDecls.put(sig, decl);
        context.addFunctionDeclaration(decl);

        if (sig instanceof Sig.PrimSig) {
            Sig.PrimSig primSig = (Sig.PrimSig) sig;

            // Translate all its children so we can translate membership in them
            for (Sig.PrimSig child : primSig.children()) {
                recursivelyTranslate(child, context);
            }

            // Add all the axioms specifying relations between the sig and its children
            sigAxioms.addPrimSigChildrenAxioms(primSig, context);

            // Generate scope constraints - note that subset sigs have no scope constraints
            // Note: if we're using Fortress scopes instead, MembershipPredicateOptTranslator handles it.
            int scope = context.scoper.sig2scope(sig);
            if (scope == -1) {
                // -1 is returned when scoper doesn't know the correct scope - fail loudly instead of silently
                throw new ErrorFatal(
                        "Cannot generate scope axiom for sig " + sig.label + " because scope is unknown");
            }
            if (context.scoper.isExact(sig)) {
                context.addAxiom(scopeAxiomStrategy.makeExactScopeAxiom(sig, scope, topLevelTranslator, context));
            } else if (scope < sortPolicy.getSortScope(sigSort)) {
                // If the sig's scope is equal to the sort's scope, then we don't need an axiom to bound the number of
                // atoms in the sort that can be in the membership predicate, because they all could be.
                // So no axiom is necessary.
                context.addAxiom(scopeAxiomStrategy.makeNonExactScopeAxiom(
                        sig, scope, topLevelTranslator, context));
            }

            // The sig's scope has to be exact since we're using a membership predicate and the scope axiom
            // strategies require it.
            // TODO: this is an implementation detail of cardinality and constants scope axiom strategies,
            //   but it should be fine for now
            context.forceSortExact(sigSort);
        } else if (sig instanceof Sig.SubsetSig) {
            Sig.SubsetSig subsetSig = (Sig.SubsetSig) sig;

            // Assert the sig is a subset of its parents (or exactly its parents if exact)
            // Note: subsetSig.exact will be true iff it's declared like "sig C = A + B {}" (valid Alloy!)
            context.addAxiom(sigAxioms.makeSubsetAxiom(subsetSig.parents, subsetSig, subsetSig.exact, context));
        } else {
            throw new ErrorFatal("Unsupported sig type!");
        }

        // Handle one, lone, some sigs
        sigAxioms.addSigMultiplicityAxiom(sig, context);

        // return Top because the returned Term doesn't matter for a Sig
        return Term.mkTop();
    }

    /** Translate "term \in sig". */
    @Override
    public Term translate(AnnotatedTerm term, Sig sig, TranslationContext context) {
        // Special cases: builtin sigs
        if (sig.builtin) {
            if (sig.equals(Sig.UNIV)) {
                // "var \in univ" is always true
                return Term.mkTop();
            } else if (sig.equals(Sig.NONE)) {
                // "var \in none" is always false
                return Term.mkBottom();
            } else if (sig.equals(Sig.SIGINT)) {
                // it's an int iff its sort is int - evaluate at compile time using var's type
                return term.getSort().equals(Sort.Int()) ? Term.mkTop() : Term.mkBottom();
            } else if (sig.equals(Sig.SEQIDX)) {
                // seq/Int is just ints in [0, maxseq-1] - TODO optimize sequences
                // Note: we use "<= maxseq - 1" and not "< maxseq" to support the case where
                // maxseq = 2^(bitwidth-1), so maxseq isn't representable in the bitwidth but maxseq-1 is.
                if (term.getSort().equals(Sort.Int())) {
                    return Term.mkAnd(
                            Term.mkGE(term.getTerm(), IntegerLiteral.apply(0)),
                            Term.mkLE(term.getTerm(), IntegerLiteral.apply(context.getMaxSeq() - 1)));
                } else {
                    return Term.mkBottom();
                }
            } else if (sig.equals(Sig.STRING)) {
                // TODO - implement strings for real
                return Term.mkBottom();
            } else {
                throw new ErrorNoPortusSupport("Unsupported builtin sig: " + sig);
            }
        }

        // If we recognize the sig, use its membership predicate
        if (!sigMemberPredicates.containsKey(sig)) {
            throw new ErrorFatal("Unknown sig " + sig);
        }
        return sigMemberPredicates.get(sig).apply(term);
    }

    /** Translate a field declaration inside a sig. */
    @Override
    public Term translate(Sig.Field field, TranslationContext context) {
        // Find the Fortress sorts corresponding to the arguments of this field's predicate.
        // Fields must have all definite sorts.
        List<Sort> argSorts = sortPolicy.getMinimalExprDefiniteSorts(field,
                "A field declaration must have definite Portus sorts!", context);

        // Make a new predicate for the field relation (function optimization is elsewhere).
        String relName = nameGenerator.freshName(field.label);
        relationPredicates.put(field, terms -> {
            if (terms.size() != field.type().arity()) {
                throw new ErrorFatal("Field predicate arity mismatch: expected arity " + field.type().arity()
                        + " but got " + terms.size() + ".");
            }
            if (!terms.getSorts().equals(argSorts)) {
                // Sorts don't match, so it's definitely not in the field!
                return Term.mkBottom();
            }
            return Term.mkApp(relName, terms.getTerms());
        });

        // the predicate signature is S1->S2->...->Sn->Bool, where Si is the ith product type's sort
        FuncDecl decl = FuncDecl.mkFuncDecl(relName, argSorts, Sort.Bool());
        relationPredicateDecls.put(field, decl);
        context.addFunctionDeclaration(decl);

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
                .map(sort -> Term.mkVar(nameGenerator.freshName("x")).of(sort))
                .collect(Collectors.toList());
        Term domainAxiom;
        try {
            context.addFortressVars(vars);
            domainAxiom = Term.mkForall(vars, Term.mkImp(
                recursivelyTranslate(ExprElementOf.make(TermTuple.fromVars(vars), field), context),
                recursivelyTranslate(ExprElementOf.make(vars.get(0), field.sig), context)));
        } finally {
            context.removeFortressVars(vars);
        }

        return Term.mkAnd(domainAxiom, rangeAxiom);
    }

    /** Evaluate a sig given a solution. */
    private ValueTupleSet evaluateSig(Sig sig, FortressSolution solution) {
        // Evaluate only sigs which we've translated here
        if (!sigMemberPredicateDecls.containsKey(sig)) return null; // not translated here

        // Take the preimage of "true" in the predicate.
        return solution.functionPreimage(sigMemberPredicateDecls.get(sig), Term.mkTop());
    }

    private ValueTupleSet evaluateField(Sig.Field field, FortressSolution solution) {
        // Evaluate only fields we've translated here
        if (!relationPredicateDecls.containsKey(field)) return null;

        // Take the preimage of "true" in the relation predicate.
        return solution.functionPreimage(relationPredicateDecls.get(field), Term.mkTop());
    }

    @Override
    public Term translate(TermTuple tuple, Sig.Field field, TranslationContext context) {
        // if we recognize the field, use its relation
        if (!relationPredicates.containsKey(field)) {
            throw new ErrorFatal("Unknown field: " + field);
        }
        return relationPredicates.get(field).apply(tuple);
    }

    /** Translate "tuple \in expr", where expr is an ExprBinary term. */
    @Override
    public Term translate(TermTuple tuple, ExprBinary expr, TranslationContext context) {
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
                return Term.mkEq(tuple.getTerm(0), translateArithmeticOperation(
                        expr.op, expr.left, expr.right, context));
            default:
                // others are either not supported or not terms
                throw new ErrorNoPortusSupport("Unsupported ExprBinary term: " + expr.op);
        }
    }

    /** Translate "tuple \in left + right". */
    private Term translateUnion(TermTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkOr(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    /** Translate "tuple \in left & right". */
    private Term translateIntersection(TermTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                recursivelyTranslate(ExprElementOf.make(tuple, right), context));
    }

    private Term translateSetDifference(TermTuple tuple, Expr left, Expr right, TranslationContext context) {
        // see KT figure 4.10
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(tuple, left), context),
                Term.mkNot(recursivelyTranslate(ExprElementOf.make(tuple, right), context)));
    }

    /** Translate "tuple \in left . right". */
    private Term translateJoin(TermTuple tuple, Expr left, Expr right, TranslationContext context) {
        // Naive join implementation without optimizations (see KT figure 4.11).
        // [[(x1,...,xn) \in e1 . e2]] := exists y: sort . [[(x1,...,xm,y) \in e1]] &&
        //   [[(y,x{m+1},...,xn) \in e2]] where arity(e1) = m+1 and arity(e2) = n-m+1 and m<n
        Var yVar = Term.mkVar(nameGenerator.freshName("y"));

        // Determine the sort that y should have.
        int partitionIdx = left.type().arity() - 1; // so that adding y gives the arity
        SortResolvant leftSort = sortPolicy.getMinimalExprSorts(left, context);
        SortResolvant rightSort = sortPolicy.getMinimalExprSorts(right, context);

        // The arity of the tuple must match that of the joined exprs.
        if (tuple.size() != leftSort.arity() + rightSort.arity() - 2) {
            throw new ErrorFatal("Tuple's arity does not match join arity!");
        }

        // Some sort tuple possibilities on the left and right cannot possibly be used because they do not match the
        // tuple. Therefore, we can eliminate them from the sort resolvants (effectively short-circuiting them out).
        // This expands the number of cases we are able to handle (e.g. (*f).(*g)).
        List<Sort> leftTupleSorts = tuple.slice(0, leftSort.arity() - 1).getSorts();
        List<Sort> rightTupleSorts = tuple.slice(leftSort.arity() - 1, tuple.size()).getSorts();
        leftSort = leftSort.filter(sortsOption -> SetOps.startsWith(sortsOption, leftTupleSorts));
        rightSort = rightSort.filter(sortsOption -> SetOps.endsWith(sortsOption, rightTupleSorts));

        // If either sort statically resolves to none, then everything is none because none.x = x.none = none.
        // So we can short-circuit to false. Similarly, if the join statically resolves to none, there's no overlap,
        // so we can short-circuit again to false.
        if (leftSort.isNone() || rightSort.isNone() || leftSort.join(rightSort).isNone()) {
            return Term.mkBottom();
        }

        // Otherwise, there is an intersection between the middle columns. We can translate if the intersection is
        // exactly one sort, because then all possible common y values come from that sort.
        Set<Sort> middleIntersection = SetOps.intersection(
                leftSort.getSortsInColumn(leftSort.arity() - 1),
                rightSort.getSortsInColumn(0));
        if (middleIntersection.size() != 1) {
            throw new ErrorNoPortusSupport("Joined columns must intersect in one Portus sort!");
        }
        Sort ySort = middleIntersection.iterator().next(); // get the single value
        AnnotatedVar y = yVar.of(ySort);

        // build up the tuples we'll recurse on
        // append y to make (x1, ..., xm, y)
        TermTuple leftSubTuple = tuple.slice(0, partitionIdx).concat(TermTuple.fromVars(y));
        // prepend y to make (y, x{m+1}, ..., xn)
        TermTuple rightSubTuple = TermTuple.fromVars(y).concat(tuple.slice(partitionIdx, tuple.size()));

        try {
            context.addFortressVar(y);
            //noinspection SuspiciousNameCombination - IntelliJ is overzealous
            return Term.mkExists(y, Term.mkAnd(
                    recursivelyTranslate(ExprElementOf.make(leftSubTuple, left), context),
                    recursivelyTranslate(ExprElementOf.make(rightSubTuple, right), context)));
        } finally {
            context.removeFortressVar(y);
        }
    }

    /** Translate "tuple \in left->right". */
    private Term translateCrossProduct(TermTuple tuple, Expr left, Expr right, TranslationContext context) {
        // [[(x1,...,xn) \in e1->e2]] := [[(x1,...,xm) \in e1]] && [[(x{m+1},...,xn) \in e2]]
        // where arity(e1) = m and arity(e2) = n-m
        if (left.type().arity() + right.type().arity() != tuple.size()) {
            throw new ErrorFatal("Cross product arities do not match!");
        }

        TermTuple leftSubTuple = tuple.slice(0, left.type().arity());
        TermTuple rightSubTuple = tuple.slice(left.type().arity(), tuple.size());
        return Term.mkAnd(
                recursivelyTranslate(ExprElementOf.make(leftSubTuple, left), context),
                recursivelyTranslate(ExprElementOf.make(rightSubTuple, right), context));
    }

    /** Translate the formula "tuple \in domain <: expr". */
    private Term translateDomainRestriction(TermTuple tuple, Expr domain, Expr expr, TranslationContext context) {
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
    private Term translateRangeRestriction(TermTuple tuple, Expr expr, Expr range, TranslationContext context) {
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
    private Term translateOverride(TermTuple tuple, Expr base, Expr override, TranslationContext context) {
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

        // TODO: the *first* index doesn't actually need a definite sort, can we not require it?
        List<Sort> overrideSorts = sortPolicy.getMinimalExprDefiniteSorts(override,
                "The second argument to ++ must have definite Portus sorts!", context);

        // build up the terms x1,y2,...,yn and the annotated vars y2,...,yn
        List<AnnotatedVar> quantifiedVars = new ArrayList<>();
        List<AnnotatedTerm> allTerms = new ArrayList<>();
        allTerms.add(tuple.getAnnotatedTerm(0));
        for (int i = 1; i < arity; i++) {
            Var yVar = Term.mkVar(nameGenerator.freshName("y" + i));
            // TODO: how much short circuiting can we do here?
            AnnotatedVar y = yVar.of(overrideSorts.get(i));
            quantifiedVars.add(y);
            allTerms.add(new AnnotatedTerm(y));
        }

        // translate [[(x1,y2,...,yn) \in override]]
        Term firstInOverride;
        try {
            context.addFortressVars(quantifiedVars);
            firstInOverride = recursivelyTranslate(
                    ExprElementOf.make(new TermTuple(allTerms), override), context);
        } finally {
            context.removeFortressVars(quantifiedVars);
        }

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
                sortPolicy.checkIsFormula("'=>' requires formulas on both sides", expr.left, expr.right);
                return Term.mkImp(
                        recursivelyTranslate(expr.left, context),
                        recursivelyTranslate(expr.right, context));
            case IFF:
                sortPolicy.checkIsFormula("'<=>' requires formulas on both sides", expr.left, expr.right);
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
                // "x.y" might be an integer expression, but we handle it elsewhere because it needs scalars
                return null;
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
        // The meaning is [[e1 in M e2]] := [[M e1]] && [[e1 in e2]].

        SortResolvant e1Sorts = sortPolicy.getMinimalExprSorts(e1, context);
        SortResolvant e2Sorts = sortPolicy.getMinimalExprSorts(e2, context);
        if (e1Sorts.arity() != e2Sorts.arity()) { // typechecker should have ensured this
            throw new ErrorNoPortusSupport("Both sides in an 'in' or '=' formula must have the same arity!");
        }

        // "exactly" is used in the meta feature and means to treat "in exactly" like "=" as a hack
        boolean isEquals = (op == ExprBinary.Op.EQUALS || e2.mult() == ExprUnary.Op.EXACTLYOF);

        // Additional condition [[M e1]] for [[e1 in M e2]]
        Term multCond = isEquals ? Term.mkTop() : getMultCondition(e1, e2, context);

        // Short-circuit if either expression statically resolves to none.
        if (e1Sorts.isNone() && e2Sorts.isNone()) {
            // If both are none, then the expression is "M none and none =/in none", which short-circuits to "M none".
            return multCond;
        } else if (e1Sorts.isNone() || e2Sorts.isNone()) {
            // If one is none, then apply the following simplifications:
            //     [[none in e]] := true
            //     [[e in none]] = [[e = none]] = [[none = e]] := [[no e]]
            if (!isEquals && e1Sorts.isNone()) {
                return multCond;
            } else {
                Expr nonNoneExpr = e1Sorts.isNone() ? e2 : e1;
                return Term.mkAnd(recursivelyTranslate(nonNoneExpr.no(), context), multCond);
            }
        }

        // If the sets of sort tuples are disjoint, there's no possible overlap between e1 and e2. Then:
        // - for "e1 = e2", both e1 and e2 must be empty
        // - for "e1 in M e2", e1 must be empty and the multiplicity condition must be true
        SortResolvant intersection = e1Sorts.intersection(e2Sorts);
        if (intersection.isNone()) {
            if (isEquals) {
                return recursivelyTranslate(e1.no().and(e2.no()), context);
            } else {
                return Term.mkAnd(recursivelyTranslate(e1.no(), context), multCond);
            }
        }

        // For "e1 = e2", we require e1 and e2 to have the same definite sorts.
        // For "e1 in M e2", we require only that e1 has definite sorts that are a subset of e2's.
        if (isEquals) {
            // Note: since the intersection of e1Sorts and e2Sorts is not empty, if both sorts are definite,
            // then they're equal.
            if (!e1Sorts.isDefinite() || !e2Sorts.isDefinite()) {
                throw new ErrorNoPortusSupport("Both sides of an '=' formula must have definite Portus sorts!");
            }
        } else {
            // Note: we know the intersection of e1Sorts and e2Sorts is not empty, so if e1Sorts is definite
            // (i.e., there is only one sort tuple), then e1Sorts must be a subset of e2Sorts.
            if (!e1Sorts.isDefinite()) {
                throw new ErrorNoPortusSupport("The LHS of an 'in' formula must have definite Portus sorts!");
            }
        }

        // We'll use e1's sorts regardless for the variables.
        List<Sort> sorts = e1Sorts.getDefiniteSorts();

        // Create the variables
        List<AnnotatedVar> vars = IntStream.range(0, e1.type().arity())
                .mapToObj(idx -> Term.mkVar(nameGenerator.freshName("x" + idx))
                        .of(sorts.get(idx)))
                .collect(Collectors.toList());

        Term inE1, inE2;
        try {
            context.addFortressVars(vars);
            inE1 = recursivelyTranslate(ExprElementOf.make(TermTuple.fromVars(vars), e1), context);
            inE2 = recursivelyTranslate(ExprElementOf.make(TermTuple.fromVars(vars), e2), context);
        } finally {
            context.removeFortressVars(vars);
        }

        if (isEquals) {
            return Term.mkForall(vars, Term.mkIff(inE1, inE2));
        } else { // ExprBinary.Op.IN
            return Term.mkAnd(
                    Term.mkForall(vars, Term.mkImp(inE1, inE2)),
                    // Add the additional condition for "e1 in M e2"
                    multCond);
        }
    }

    /** Get the multiplicity condition that must be true for an "e1 in M e2" condition to hold. */
    private Term getMultCondition(Expr e1, Expr e2, TranslationContext context) {
        switch (e2.mult()) {
            case ONEOF:
                return recursivelyTranslate(e1.one(), context);
            case LONEOF:
                return recursivelyTranslate(e1.lone(), context);
            case SOMEOF:
                return recursivelyTranslate(e1.some(), context);
            default:
                return Term.mkTop();
        }
    }

    /** Translate "lhs op rhs", where op is an arithmetic comparison like <, >, =<, >=.  */
    private Term translateArithmeticComparison(ExprBinary.Op op, Expr lhs, Expr rhs, TranslationContext context) {
        sortPolicy.checkIsInt(op + " requires both sides to be integers!", lhs, rhs);

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
                throw new ErrorNoPortusSupport("Unsupported arithmetic comparison operator: " + op);
        }
    }

    /** Translate "lhs op rhs", where op is an arithmetic operation. */
    private Term translateArithmeticOperation(ExprBinary.Op op, Expr lhs, Expr rhs, TranslationContext context) {
        sortPolicy.checkIsInt(op + " requires both sides to be integer expressions!", lhs, rhs);

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
                throw new ErrorNoPortusSupport("Unsupported arithmetic operation: " + op);
        }
    }

    /** Translate the formula (or int expression) "f1 => f2 else f3". */
    @Override
    public Term translate(ExprITE expr, TranslationContext context) {
        // use Fortress's built-in if-then-else
        sortPolicy.checkIsFormula("The condition of if-then-else must be a formula!", expr.cond);
        Term cond = recursivelyTranslate(expr.cond, context);
        Term left = recursivelyTranslate(expr.left, context);
        Term right = recursivelyTranslate(expr.right, context);
        return Term.mkIfThenElse(cond, left, right);
    }

    /** Translate the formula "tuple \in (f => e1 else e2)". */
    @Override
    public Term translate(TermTuple tuple, ExprITE expr, TranslationContext context) {
        // Similar to the above: "IfThenElse([[f]], [[tuple \in e1]], [[tuple \in e2]])"
        sortPolicy.checkIsFormula("The condition of if-then-else must be a formula!", expr.cond);
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
                sortPolicy.checkIsFormula("The argument of '!' must be a formula!", expr.sub);
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
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (resolvant.isNone()) {
            // Short-circuit: [[#none]] = 0
            return IntegerLiteral.apply(0);
        }
        if (!resolvant.isDefinite()) {
            throw new ErrorNoPortusSupport("Argument of cardinality must have definite sorts!");
        }
        List<Sort> sorts = resolvant.getDefiniteSorts();

        List<AnnotatedVar> vars = new ArrayList<>();
        for (int i = 0; i < expr.type().arity(); i++) {
            Var var = Term.mkVar(nameGenerator.freshName("x" + i));
            vars.add(var.of(sorts.get(i)));
        }

        try {
            context.addFortressVars(vars);
            Term condition = recursivelyTranslate(ExprElementOf.make(TermTuple.fromVars(vars), expr), context);
            return translateSum(IntegerLiteral.apply(1), condition, vars, context);
        } finally {
            context.removeFortressVars(vars);
        }
    }

    /** Translate "tuple \in expr", where expr is an ExprUnary formula. */
    @Override
    public Term translate(TermTuple tuple, ExprUnary expr, TranslationContext context) {
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
    private Term translateTranspose(TermTuple tuple, Expr sub, TranslationContext context) {
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Transpose argument must have arity 2");
        }

        // swap the variables in the tuple - see KT figure 4.11
        TermTuple swapped = tuple.pick(1).concat(tuple.pick(0));
        return recursivelyTranslate(ExprElementOf.make(swapped, sub), context);
    }

    /** Translate "tuple \in ^sub" (reflexive==false) or "tuple \in *sub" (reflexive==true). */
    private Term translateClosure(boolean reflexive, TermTuple tuple, Expr sub, TranslationContext context) {
        if (tuple.size() != 2) {
            throw new ErrorSyntax("Closure argument must have arity 2");
        }

        // If the sorts aren't the same, we can't translate.
        // (We can't short-circuit: consider (a,b) \in ^iden vs (a,b) \in ^(univ->univ) where a,b have different sorts)
        if (!tuple.getSort(0).equals(tuple.getSort(1))) {
            throw new ErrorNoPortusSupport(
                    "Portus doesn't support transitive closure with distinct Fortress sorts!");
        }
        Sort commonSort = tuple.getSort(0);

        // Translate as "^f(x,y)" or "*f(x,y)" where f is an auxiliary relation f(x,y) = [[(x,y) \in sub]].
        // Also include all the free variables as secondary arguments.
        String auxRelationName = makeClosureBinaryRelation(commonSort, sub, context);
        List<Term> freeVars = PortusUtil.computeFreeVariables(sub, context, sortPolicy).stream()
                .map(AnnotatedVar::variable)
                .collect(Collectors.toList());
        if (reflexive) {
            return Term.mkReflexiveClosure(auxRelationName, tuple.getTerm(0), tuple.getTerm(1), freeVars);
        } else {
            return Term.mkClosure(auxRelationName, tuple.getTerm(0), tuple.getTerm(1), freeVars);
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
            if (field.type().arity() == 2 && relationPredicateDecls.containsKey(field)) {
                return relationPredicateDecls.get(field).name();
            }
        }

        // Have we already translated this expr/sort combo? If so, use its name.
        String cachedName = auxClosureRelationNames.get(expr, sort, context);
        if (cachedName != null) {
            return cachedName;
        }

        if (!expr.type().hasArity(2)) {
            throw new ErrorSyntax("We can only take the transitive/reflexive closure of binary expressions.");
        }

        // Define an auxiliary relation f(x,y) = [[(x,y) \in expr]] of type sort->sort
        // Use a definition because otherwise we'd need an expensive axiom.
        // Also include any free variables in the term as extra arguments.
        String auxRelationName = nameGenerator.freshName("closureAux_" + sort.name());
        auxClosureRelationNames.put(expr, sort, auxRelationName, context);

        // The type of the aux relation is (sort,sort,*extras)->Bool
        List<AnnotatedVar> freeVars = PortusUtil.computeFreeVariables(expr, context, sortPolicy);
        Var x = Term.mkVar(nameGenerator.freshName("x"));
        Var y = Term.mkVar(nameGenerator.freshName("y"));
        List<AnnotatedVar> decls = new ArrayList<>(Arrays.asList(x.of(sort), y.of(sort)));
        decls.addAll(freeVars);

        try {
            // Only add mappings for x and y because the rest should be covered by the free variables.
            // TODO: If this causes bugs, use a fresh var mapping context for the definition.
            context.addFortressVars(x.of(sort), y.of(sort));
            Term inExpr = recursivelyTranslate(ExprElementOf.make(
                    TermTuple.fromVars(x.of(sort), y.of(sort)), expr), context);
            FunctionDefinition auxDefn = FunctionDefinition.mkFunctionDefinition(
                    auxRelationName, decls, Sort.Bool(), inExpr);
            context.addFunctionDefinition(auxDefn);
        } finally {
            context.removeFortressVars(x.of(sort), y.of(sort));
        }

        return auxRelationName;
    }

    /** Translate an ExprList formula. */
    @Override
    public Term translate(ExprList expr, TranslationContext context) {
        if (expr.op == ExprList.Op.DISJOINT) {
            return translateDisjoint(expr.args, context);
        } else if (expr.op == ExprList.Op.TOTALORDER) {
            throw new ErrorNoPortusSupport("Portus does not yet support TOTALORDER");
        }

        // first, just translate all the args (they all must be formulas)
        sortPolicy.checkIsFormula("AND or OR arguments must all be formulas", expr.args);
        List<Term> translatedArgs = expr.args.stream()
                .map(arg -> recursivelyTranslate(arg, context))
                .collect(Collectors.toList());

        switch (expr.op) {
            // see KT figure 4.6, extended to any number of ops
            // note that an empty AND list is always true, and an empty OR list is always false
            case AND:
                return translatedArgs.isEmpty() ? Term.mkTop() : Term.mkAnd(translatedArgs);
            case OR:
                return translatedArgs.isEmpty() ? Term.mkBottom() : Term.mkOr(translatedArgs);
            default:
                // we don't yet support DISJOINT or TOTALORDER
                throw new ErrorNoPortusSupport("Unsupported ExprList formula: " + expr.op);
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
        List<AnnotatedTerm> terms = args.stream().map(arg -> {
            if (arg instanceof ExprVar) {
                ExprVar var = (ExprVar) arg;
                if (context.hasTermMapping(var.label)) {
                    return context.getTermMapping(var.label);
                }
            }
            throw new ErrorNoPortusSupport("Portus only supports disj[] with bound variables.");
        }).collect(Collectors.toList());

        // Make sure they have the same sort - we don't support it if they don't.
        // (If we do have to support this - partition by sort and map to a conjunction of distincts.)
        if (terms.stream().map(AnnotatedTerm::getSort).distinct().count() > 1) {
            throw new ErrorNoPortusSupport(
                    "Portus only supports disj[] with variables of the same top-level sort.");
        }

        return Term.mkDistinct(terms.stream().map(AnnotatedTerm::getTerm).collect(Collectors.toList()));
    }

    /** Translate "Q e", where Q is one of {one, lone, some, no} and e is an expression. */
    private Term translateQuantifiedExpr(ExprQt.Op quantifier, Expr expr, TranslationContext context) {
        // "Q e" is equivalent to "Q x1:S1,...,xn:Sn | (x1,...,xn) \in e" where n = arity(e), so translate as such
        // for simplicity.
        int arity = expr.type().arity();
        if (arity <= 0) {
            throw new ErrorNoPortusSupport("Portus doesn't support types with multiple arities");
        }
        List<AnnotatedVar> vars = new ArrayList<>(arity);

        SortResolvant exprResolvant = sortPolicy.getMinimalExprSorts(expr, context);

        if (exprResolvant.isNone()) {
            // Short-circuit if we're quantifying over none
            // [[one none]] = [[some none]] = false
            // [[no none]] = [[lone none]] = true
            switch (quantifier) {
                case ONE:
                case SOME:
                    return Term.mkBottom();
                case NO:
                case LONE:
                    return Term.mkTop();
                default:
                    throw new ErrorFatal("Invalid quantifier for quantified expression: " + quantifier);
            }
        }

        // Otherwise, we can only translate definite sorts
        if (!exprResolvant.isDefinite()) {
            throw new ErrorNoPortusSupport("Quantified expressions must have definite sorts!");
        }
        List<Sort> exprSorts = exprResolvant.getDefiniteSorts();

        for (int i = 0; i < arity; i++) {
            Var var = Term.mkVar(nameGenerator.freshName("x" + i));
            vars.add(var.of(exprSorts.get(i)));
        }

        // technically, we actually translate as pseudo-Alloy "Q (x1,...,xn): e | true", so there's an extra true
        Term condition;
        try {
            context.addFortressVars(vars);
            condition = recursivelyTranslate(ExprElementOf.make(TermTuple.fromVars(vars), expr), context);
        } finally {
            context.removeFortressVars(vars);
        }
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

        // Check if any of the decls statically resolve to none - if so, we can short-circuit.
        boolean isNone = expr.decls.stream()
                .map(decl -> sortPolicy.getMinimalExprSorts(decl.expr, context))
                .anyMatch(SortResolvant::isNone);
        if (isNone) {
            // One of the things we're quantifying over is none: short-circuit.
            switch (expr.op) {
                case ALL: // "all x: none | f" is vacuously true
                case NO:
                case LONE:
                    return Term.mkTop();
                case SOME:
                case ONE:
                    return Term.mkBottom();
                case SUM:
                    // Easiest to handle here: empty sum is 0
                    return IntegerLiteral.apply(0);
                default:
                    throw new ErrorFatal("Unknown quantifier for formulas: " + expr.op);
            }
        }

        // Translate all the decls into Fortress
        Pair<Pair<List<String>, List<AnnotatedVar>>, AnnotatedTerm> varsAndCond =
                PortusUtil.translateDeclList(expr.decls, context, sortPolicy, topLevelTranslator, nameGenerator);
        List<String> alloyVarNames = varsAndCond.a.a;
        List<AnnotatedVar> vars = varsAndCond.a.b;
        Term condition = varsAndCond.b.getTerm();

        // Process subformula - Fortress vars were added to the lexical scope in translateDeclList()
        try {
            Term sub = recursivelyTranslate(expr.sub, context);
            return translateRawQuantifier(expr.op, vars, condition, sub, context);
        } finally {
            // Remove the vars from the lexical scope since it's done (always, even if there's an exception)
            for (String alloyVarName : alloyVarNames) {
                context.removeMapping(alloyVarName);
            }
            context.removeFortressVars(vars);
        }
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
                throw new ErrorFatal("Unsupported quantifier: " + quantifier);
        }
    }

    // Translate "sum x: e | f" where sub translates [[f]] and condition translates [[x \in e]].
    private Term translateSum(Term sub, Term condition, List<AnnotatedVar> vars, TranslationContext context) {
        // naive for now: manually expand "sum y: sort | [[y \in e]] => [[f[y/x]]] else 0"
        // nest the additions naively left-to-right: ((((1 + 1) + 1) + 1) + ...)
        List<Sort> sorts = new ArrayList<>();
        for (AnnotatedVar var : vars) {
            Sort sort = var.sort();
            sorts.add(sort);

            if (!sort.equals(Sort.Int())) {
                // We're expanding over the domain elements of the sort, so its scope can't be changed arbitrarily
                // in the output - mark it unchanging
                context.markSortUnchanging(sort);
            }
        }

        // Use a final one-element array to get around Java limitations: only final vars can be used in lambdas.
        final Term[] result = {null};
        PortusUtil.expandOverSorts(sorts, sortPolicy, tuple -> {
            Term domElemCondition = PortusUtil.substitute(vars, tuple, condition);
            Term domElemSub = PortusUtil.substitute(vars, tuple, sub);

            // add "condition => sub else 0" to the result
            Term addend = Term.mkIfThenElse(domElemCondition, domElemSub, IntegerLiteral.apply(0));
            if (result[0] == null) {
                result[0] = addend;
            } else {
                result[0] = Term.mkPlus(result[0], addend);
            }
        });
        return result[0];
    }

    @Override
    public Set<Sort> determineExpandedSorts(Expr expr, VarMappingContext varMappingContext) {
        // A sort is unchanging, for our purposes, if we have to expand over it due to cardinality or sum.
        // TODO: TEST THIS WITH NONE!
        if (expr instanceof ExprUnary) {
            ExprUnary exprUnary = (ExprUnary) expr;
            if (exprUnary.op == ExprUnary.Op.CARDINALITY) {
                SortResolvant resolvant = sortPolicy.getMinimalExprSorts(exprUnary.sub, varMappingContext);
                if (resolvant.isNone()) {
                    // special case, "#none" - don't worry about it
                    return new HashSet<>();
                }
                if (!resolvant.isDefinite()) {
                    throw new ErrorNoPortusSupport("Argument of cardinality must have definite sorts!");
                }
                return new HashSet<>(resolvant.getDefiniteSorts());
            }
        } else if (expr instanceof ExprQt) {
            ExprQt exprQt = (ExprQt) expr;
            if (exprQt.op == ExprQt.Op.SUM) {
                // If any of them are none, we don't have to expand over anything
                boolean anyNone = exprQt.decls.stream()
                        .map(decl -> sortPolicy.getMinimalExprSorts(decl.expr, varMappingContext))
                        .anyMatch(SortResolvant::isNone);
                if (anyNone) {
                    return new HashSet<>();
                }

                // Otherwise, everything has to have definite sorts.
                return exprQt.decls.stream()
                        .map(decl -> decl.expr)
                        .flatMap(declExpr -> {
                            List<Sort> sorts = sortPolicy.getMinimalExprDefiniteSorts(declExpr,
                                    "Quantifier argument formula must have definite sorts!", varMappingContext);
                            return sorts.stream();
                        })
                        .collect(Collectors.toSet());
            }
        }
        return new HashSet<>();
    }

    /** Translate "tuple \in expr", where expr is an ExprQt. */
    @Override
    public Term translate(TermTuple tuple, ExprQt expr, TranslationContext context) {
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
    private Term translateComprehension(TermTuple tuple, ExprQt expr, TranslationContext context) {
        // [[(x1,...,xn) \in {y1: e1, ..., yn: en | f(y1,...,yn)}]] :=
        // [[x1 \in e1 and (let y1=x1 | x2 \in e2 and (let y2=x2 | ... (let yn=xn | f(y1,...,yn))))]]
        // But we translate more like [[x1 \in e1]] && ... && [[xn \in en]] && [[f(y1,...,yn)]]
        // and do the let mappings manually.
        // First, check the arity is correct
        if (tuple.size() != expr.count()) {
            throw new ErrorSyntax("Mismatched arity for comprehension expression!");
        }

        // Pair the terms and decls/names
        List<Pair<AnnotatedTerm, Pair<Decl, ExprHasName>>> termsAndDecls = new ArrayList<>();
        int tupleIdx = 0;
        for (Decl decl : expr.decls) {
            for (ExprHasName name : decl.names) {
                AnnotatedTerm var = tuple.getAnnotatedTerm(tupleIdx);
                termsAndDecls.add(new Pair<>(var, new Pair<>(decl, name)));
                tupleIdx++;
            }
        }

        List<Term> conjuncts = new ArrayList<>();

        // Generate each [[xi \in ei]] conjunct
        for (Pair<AnnotatedTerm, Pair<Decl, ExprHasName>> termAndDecl : termsAndDecls) {
            AnnotatedTerm term = termAndDecl.a;
            Decl decl = termAndDecl.b.a;
            ExprHasName name = termAndDecl.b.b;
            // Unwrap the expression from its multiplicity (and any NOOPs)
            Expr declExpr = decl.expr.deNOP();
            if (declExpr.mult == 1) {
                // We know this is an ExprUnary because decl.expr.mult() must return ONEOF,
                // because ExprQt doesn't allow comprehension decls to have other multiplicities.
                ExprUnary wrappedDeclExpr = (ExprUnary) declExpr;
                declExpr = wrappedDeclExpr.sub;
            }
            Expr conjunct = ExprElementOf.make(term, declExpr);
            conjuncts.add(recursivelyTranslate(conjunct, context));

            // Map yi to xi for subsequent translations and the f(y1,...,yn) translation
            // We do this here because yi could appear in subsequent ei's and should be mapped to xi
            context.addTermMapping(name.label, term);
        }

        // Map [[f(y1,...,yn)]]
        try {
            conjuncts.add(recursivelyTranslate(expr.sub, context));
        } finally {
            // Unmap all the yi's (and do it even if there's an exception)
            for (Pair<AnnotatedTerm, Pair<Decl, ExprHasName>> termAndDecl : termsAndDecls) {
                ExprHasName name = termAndDecl.b.b;
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
    public Term translate(TermTuple tuple, ExprLet let, TranslationContext context) {
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
    public Term translate(TermTuple tuple, ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            VarMappingContext.LetContext letContext = context.getLetMapping(expr.label);
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
        AnnotatedTerm mapped = checkAndMapVarName(expr.label, context);
        // If the sorts are mismatched, short-circuit (the tuple can't be in the expr)
        if (!tuple.getSort(0).equals(mapped.getSort())) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getTerm(0), mapped.getTerm());
    }

    /** Translate an ExprVar integer expression. */
    @Override
    public Term translate(ExprVar expr, TranslationContext context) {
        // Check if it's mapped to a let-expression - if so, use that instead
        if (context.hasLetMapping(expr.label)) {
            VarMappingContext.LetContext letContext = context.getLetMapping(expr.label);
            assert letContext != null;
            letContext.useLetMapping(context);
            try {
                return recursivelyTranslate(letContext.getExpr(), context);
            } finally {
                letContext.resetMapping();
            }
        }
        return checkAndMapVarName(expr.label, context).getTerm();
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
                PortusUtil.checkLiteralIntWithinBitwidth(expr.num, context.getBitwidth());
                return IntegerLiteral.apply(expr.num);
            case MIN:
                return IntegerLiteral.apply(Util.min(context.getBitwidth()));
            case MAX:
                return IntegerLiteral.apply(Util.max(context.getBitwidth()));
            default:
                throw new ErrorNoPortusSupport("Unsupported ExprConstant formula/int expression: " + expr);
        }
    }

    /** Translate "tuple \in expr", where expr is an ExprConstant. */
    @Override
    public Term translate(TermTuple tuple, ExprConstant expr, TranslationContext context) {
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
                throw new ErrorNoPortusSupport("Unsupported ExprConstant expression: " + expr);
        }
    }

    /** Translate "tuple \in iden". */
    private Term translateIden(TermTuple tuple) {
        // KT figure 4.12: [[(x1, x2) \in iden]] := x1 = x2
        // note that this works even for incompatible top-level sigs since we use a universal sort
        if (tuple.size() != 2) {
            throw new ErrorFatal("iden expects arity 2, but got " + tuple.size());
        }
        // if the sorts are different, then they can't be equal: short-circuit
        if (!tuple.getSort(0).equals(tuple.getSort(1))) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getTerm(0), tuple.getTerm(1));
    }

    /** Translate "tuple \in next". */
    private Term translateNext(TermTuple tuple, TranslationContext context) {
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
        Term guard = Term.mkNot(Term.mkEq(tuple.getTerm(0), IntegerLiteral.apply(max)));
        Term check = Term.mkEq(Term.mkPlus(tuple.getTerm(0), IntegerLiteral.apply(1)), tuple.getTerm(1));
        return Term.mkAnd(guard, check);
    }

    /** Translate a predicate or integer-valued function call. */
    @Override
    public Term translate(ExprCall call, TranslationContext context) {
        return translateCall(call.fun.getBody(), call, context);
    }

    /** Translate "tuple \in call", where call is a function call. */
    @Override
    public Term translate(TermTuple tuple, ExprCall call, TranslationContext context) {
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

    private Term translateInIntExpr(TermTuple tuple, Expr intExpr, TranslationContext context) {
        if (tuple.size() != 1) {
            throw new ErrorSyntax("Int expression '" + intExpr + "' requires arity 1");
        }
        // assume intExpr is really an integer expression, and short-circuit if tuple isn't of type Int
        if (!tuple.getSort(0).equals(Sort.Int())) {
            return Term.mkBottom();
        }
        return Term.mkEq(tuple.getTerm(0), recursivelyTranslate(intExpr, context));
    }

    @Override
    public ValueTupleSet evaluate(Expr expr, FortressSolution solution, TranslationContext context) {
        if (expr instanceof Sig) {
            return evaluateSig((Sig) expr, solution);
        } else if (expr instanceof Sig.Field) {
            return evaluateField((Sig.Field) expr, solution);
        }
        return null;
    }

    /** Map an Alloy variable name to a Fortress term, or throw an error. */
    private AnnotatedTerm checkAndMapVarName(String label, TranslationContext context) {
        // the Alloy variable must be mapped to a Fortress var in the current lexical scope
        if (!context.hasTermMapping(label)) {
            throw new ErrorSyntax("Unknown variable name " + label);
        }
        return context.getTermMapping(label);
    }

    /** Generate a copy of `vars` with each variable suffixed with "_prime". */
    private List<AnnotatedVar> prime(List<AnnotatedVar> vars) {
        return vars.stream()
                .map(var -> Term.mkVar(nameGenerator.freshName(var.variable().name() + "_prime")).of(var.sort()))
                .collect(Collectors.toList());
    }

}
