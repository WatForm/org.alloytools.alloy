package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Assert;
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
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import fortress.operations.Substituter;
import scala.collection.immutable.HashSet;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * General-purpose utility functions used in Portus.
 */
final class PortusUtil {

    private PortusUtil() {}

    /** Convert a java.util.Map to a scala.collection.immutable.Map. */
    public static <A, B> scala.collection.immutable.Map<A, B> toScalaMap(Map<A, B> map) {
        //noinspection unchecked
        return scala.collection.immutable.Map.from(CollectionConverters.asScala(map));
    }

    /** Strip wrappers we consider to be (pure) NOOPs: CAST2INT, CAST2SIGINT, NOOP. */
    public static Expr stripPortusNoops(Expr expr) {
        while (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            if (unary.op == ExprUnary.Op.NOOP
                || unary.op == ExprUnary.Op.CAST2INT
                || unary.op == ExprUnary.Op.CAST2SIGINT) {
                expr = unary.sub;
            } else {
                break;
            }
        }
        return expr;
    }

    /**
     * Software Abstractions, sec. 3.6.4: a "declaration formula" is a expression of the form
     * "a in b M->N c", where M and N are multiplicities, or b or c are arrow-expressions with
     * multiplicities. Return whether expr is a declaration formula.
     */
    public static boolean isDeclarationFormula(Expr expr) {
        if (!(expr instanceof ExprBinary)) return false;
        ExprBinary inExpr = (ExprBinary) expr;
        if (inExpr.op != ExprBinary.Op.IN) return false;
        return isDeclarationFormulaArrow(inExpr.right.deNOP());
    }

    /**
     * Return whether expr is the arrow expression from a declaration formula.
     */
    public static boolean isDeclarationFormulaArrow(Expr expr) {
        if (!(expr instanceof ExprBinary)) return false;
        ExprBinary arrow = (ExprBinary) expr;
        // mult == 2 means "has an arrow multiplicity constraint"
        return arrow.op.isArrow && arrow.mult == 2;
    }

    /**
     * Return the unary multiplicity operator corresponding to "M" in "M->N", or NOOP if
     * there's no multiplicity operator. Return null if arrowOp isn't an arrow operator.
     */
    @SuppressWarnings("DuplicatedCode") // IntelliJ's duplication detection is a little aggressive
    public static ExprUnary.Op getArrowLeftMultiplicity(ExprBinary.Op arrowOp) {
        if (!arrowOp.isArrow) return null;

        switch (arrowOp) {
            case ONE_ARROW_ANY:
            case ONE_ARROW_ONE:
            case ONE_ARROW_LONE:
            case ONE_ARROW_SOME:
                return ExprUnary.Op.ONE;
            case LONE_ARROW_ANY:
            case LONE_ARROW_ONE:
            case LONE_ARROW_LONE:
            case LONE_ARROW_SOME:
                return ExprUnary.Op.LONE;
            case SOME_ARROW_ANY:
            case SOME_ARROW_ONE:
            case SOME_ARROW_LONE:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOME;
            default:
                return ExprUnary.Op.NOOP;
        }
    }

    /**
     * Return the unary multiplicity operator corresponding to "N" in "M->N", or NOOP if
     * there's no multiplicity operator. Return null if arrowOp isn't an arrow operator.
     */
    @SuppressWarnings("DuplicatedCode")
    public static ExprUnary.Op getArrowRightMultiplicity(ExprBinary.Op arrowOp) {
        if (!arrowOp.isArrow) return null;

        switch (arrowOp) {
            case ANY_ARROW_ONE:
            case ONE_ARROW_ONE:
            case LONE_ARROW_ONE:
            case SOME_ARROW_ONE:
                return ExprUnary.Op.ONE;
            case ANY_ARROW_LONE:
            case ONE_ARROW_LONE:
            case LONE_ARROW_LONE:
            case SOME_ARROW_LONE:
            case ISSEQ_ARROW_LONE:
                return ExprUnary.Op.LONE;
            case ANY_ARROW_SOME:
            case ONE_ARROW_SOME:
            case LONE_ARROW_SOME:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOME;
            default:
                return ExprUnary.Op.NOOP;
        }
    }

    /**
     * Remove all multiplicities like M and N in "A M->N B", as well as nested multiplicities.
     * If it's not an arrow ExprBinary, return it unchanged.
     */
    public static Expr stripArrowMultiplicities(Expr expr) {
        if (!(expr instanceof ExprBinary)) return expr;
        ExprBinary arrow = (ExprBinary) expr;
        if (!arrow.op.isArrow) return arrow;
        // recurse to strip nested multiplicities
        return stripArrowMultiplicities(arrow.left).product(stripArrowMultiplicities(arrow.right));
    }

    /**
     * For each pair of vars (v1, v2) in zip(a, b), substitute v1 -> v2 in term.
     * We require that a and b have the same size.
     */
    public static Term substituteVars(List<AnnotatedVar> a, List<AnnotatedVar> b, Term term) {
        return substitute(a, b.stream().map(AnnotatedVar::variable).collect(Collectors.toList()), term);
    }

    /**
     * For each (var, term) pair (v, t) in zip(a, b), substitute v -> t in term.
     * We require that a and b have the same size.
     */
    public static Term substitute(List<AnnotatedVar> a, List<? extends Term> b, Term term) {
        if (a.size() != b.size()) {
            throw new IllegalArgumentException("a and b must have same size");
        }

        // TODO: can we use FastSubstituter in some cases?
        //noinspection unchecked
        NameGenerator nameGen = new IntSuffixNameGenerator(new HashSet<String>(), 0);
        for (int i = 0; i < a.size(); i++) {
            Var from = a.get(i).variable();
            Term to = b.get(i);
            term = Substituter.apply(from, to, term, nameGen);
        }
        return term;
    }

    /**
     * A convenience overload of the above for only one var/term pair.
     */
    public static Term substitute(AnnotatedVar a, Term b, Term term) {
        return substitute(Collections.singletonList(a), Collections.singletonList(b), term);
    }

    /**
     * Generate the term (v1 = u1) && (v2 = u2) && ... && (vn = un) for each pair
     * (vi, ui) in zip(a, b). We require that a and b have the same size.
     */
    public static Term mkVarsEqual(List<AnnotatedVar> a, List<AnnotatedVar> b) {
        if (a.size() != b.size()) {
            throw new IllegalArgumentException("a and b must have same size");
        }
        List<Term> conjuncts = new ArrayList<>();
        for (int i = 0; i < a.size(); i++) {
            conjuncts.add(Term.mkEq(a.get(i).variable(), b.get(i).variable()));
        }
        return Term.mkAnd(conjuncts);
    }

    /**
     * Given a current list of integers [x1,...,xn] and a list of maximums [m1,...,mn],
     * mutate current to the next element in the Cartesian product {1,...,m1}x...x{1,...,mn}.
     * Return true if we got a new combination or false if current is the last combination.
     */
    public static boolean nextCombination(List<Integer> current, List<Integer> max) {
        if (current.size() != max.size()) {
            throw new IllegalArgumentException("current and max must have the same size");
        }
        for (int i = max.size() - 1; i >= 0; i--) {
            if (current.get(i) < max.get(i)) {
                current.set(i, current.get(i) + 1);
                return true;
            } else {
                current.set(i, 1);
            }
        }
        return false;
    }

    /**
     * Convert an iterable to a list. Java doesn't make this as easy as it should be.
     */
    public static <T> List<T> iterableToList(Iterable<T> iterable) {
        List<T> list = new ArrayList<>();
        iterable.forEach(list::add);
        return list;
    }

    /**
     * Get a list of the variables which are free in the translation of expr, with sorts determined by the context
     * (which should assign a Fortress var for each free Alloy var).
     */
    public static List<AnnotatedVar> computeFreeVariables(Expr expr, final TranslationContext inContext) {
        // make a copy just in case
        TranslationContext context = new TranslationContext(inContext);

        // simple recursive implementation
        return expr.accept(new FortressVisitReturn<List<AnnotatedVar>>() {
            @SafeVarargs
            private final List<AnnotatedVar> union(List<AnnotatedVar>... lists) {
                // this is O(n^2) to union two lists of length n, but this shouldn't be a bottleneck
                List<AnnotatedVar> result = new ArrayList<>();
                for (List<AnnotatedVar> list : lists) {
                    for (AnnotatedVar var : list) {
                        if (!result.contains(var)) {
                            result.add(var);
                        }
                    }
                }
                return result;
            }

            @Override
            public List<AnnotatedVar> visit(ExprBinary x) throws Err {
                return union(visitThis(x.left), visitThis(x.right));
            }

            @Override
            public List<AnnotatedVar> visit(ExprList x) throws Err {
                //noinspection unchecked
                return union(x.args.stream()
                        .map(this::visitThis)
                        .toArray(List[]::new));
            }

            @Override
            public List<AnnotatedVar> visit(ExprCall x) throws Err {
                //noinspection unchecked
                return union(x.args.stream()
                        .map(this::visitThis)
                        .toArray(List[]::new));
            }

            @Override
            public List<AnnotatedVar> visit(ExprConstant x) throws Err {
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(ExprITE x) throws Err {
                return union(visitThis(x.cond), visitThis(x.left), visitThis(x.right));
            }

            @Override
            public List<AnnotatedVar> visit(ExprLet x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public List<AnnotatedVar> visit(ExprQt x) throws Err {
                // the quantified variables aren't free - remove them from the list
                List<AnnotatedVar> subFreeVars = visitThis(x.sub);
                List<String> quantifiedVarNames = x.decls.stream()
                        .flatMap(decl -> decl.names.stream())
                        .map(name -> name.label)
                        .collect(Collectors.toList());
                return subFreeVars.stream()
                        .filter(var -> !quantifiedVarNames.contains(var.name()))
                        .collect(Collectors.toList());
            }

            @Override
            public List<AnnotatedVar> visit(ExprUnary x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public List<AnnotatedVar> visit(ExprVar x) throws Err {
                // If there's a let mapping, use free variables existing at the point of the 'let'
                if (context.hasLetMapping(x.label)) {
                    TranslationContext.LetContext letContext = context.getLetMapping(x.label);
                    assert letContext != null;
                    try {
                        letContext.useLetMapping(context);
                        return visitThis(letContext.getExpr());
                    } finally {
                        letContext.resetMapping();
                    }
                }

                // Otherwise, it should be in the context - use it
                if (!context.hasVarMapping(x.label)) {
                    throw new ErrorFatal("Unknown variable: " + x.label);
                }
                return Collections.singletonList(context.getVarMapping(x.label));
            }

            @Override
            public List<AnnotatedVar> visit(Sig sig) throws Err {
                // sigs aren't variables
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(Sig.Field x) throws Err {
                // fields aren't variables
                return new ArrayList<>();
            }

            @Override
            public List<AnnotatedVar> visit(ExprElementOf x) throws Err {
                // treat the tuple as free vars until proven otherwise
                return union(x.tuple.getAnnotatedVars(), visitThis(x.sub));
            }

            @Override
            public List<AnnotatedVar> visit(Func x) throws Err {
                throw new ErrorFatal("Visiting Func isn't supported!");
            }

            @Override
            public List<AnnotatedVar> visit(Assert x) throws Err {
                throw new ErrorFatal("Visiting Assert isn't supported!");
            }

            @Override
            public List<AnnotatedVar> visit(Macro macro) throws Err {
                throw new ErrorFatal("Visiting Macro isn't supported!");
            }
        });
    }

    /**
     * Expand all the 'let's in an expression, for use when disambiguating expressions.
     */
    public static Expr expandLets(Expr expr, final TranslationContext originalContext) {
        // Make a copy just to be safe
        TranslationContext context = new TranslationContext(originalContext);

        // note: this is vulnerable to exponential blowup in cases like
        // let x1=A+A | let x2=x1+x1 | let x3=x2+x2 | ... | let x64=x63+x63 | f[x64]
        // which will cause us to generate a union of 2^64 A's (!!)
        // but let's assume our users aren't evil enough to do that, eh?
        return expr.accept(new FortressVisitReturn<Expr>() {
            @Override
            public Expr visit(ExprBinary x) throws Err {
                return x.op.make(null, null, visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visit(ExprList x) throws Err {
                return ExprList.make(null, null, x.op, x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()));
            }

            @Override
            public Expr visit(ExprCall x) throws Err {
                // Don't expand ExprCalls for now - this might cause us to generate some duplicate auxiliary
                // functions when translating closure, e.g.
                //   ^x   and    ^f[x] where fun f[y] { ^y }
                // will generate two different auxiliary functions, but that's okay
                return ExprCall.make(null, null, x.fun, x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()), x.extraWeight);
            }

            @Override
            public Expr visit(ExprConstant x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprITE x) throws Err {
                return ExprITE.make(null, visitThis(x.cond), visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visit(ExprLet x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public Expr visit(ExprQt x) throws Err {
                // add var mappings for the quantified variables as we move into the quantifier
                for (Decl decl : x.decls) {
                    for (ExprHasName name : decl.names) {
                        // the actual variable doesn't matter for us, make one up
                        context.addVarMapping(name.label, Term.mkVar("x").of(Sort.Int()));
                    }
                }
                try {
                    return visitThis(x.sub);
                } finally {
                    // remove the var mappings
                    for (Decl decl : x.decls) {
                        for (ExprHasName name : decl.names) {
                            context.removeMapping(name.label);
                        }
                    }
                }
            }

            @Override
            public Expr visit(ExprUnary x) throws Err {
                return visitThis(x.sub);
            }

            @Override
            public Expr visit(ExprVar x) throws Err {
                // Expand the let mapping if it has it
                if (context.hasLetMapping(x.label)) {
                    TranslationContext.LetContext letContext = context.getLetMapping(x.label);
                    assert letContext != null;
                    try {
                        letContext.useLetMapping(context);
                        return visitThis(letContext.getExpr());
                    } finally {
                        letContext.resetMapping();
                    }
                } else {
                    return x;
                }
            }

            @Override
            public Expr visit(Sig sig) throws Err {
                return sig;
            }

            @Override
            public Expr visit(Sig.Field x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprElementOf x) throws Err {
                return ExprElementOf.make(x.tuple, visitThis(x.sub));
            }

            @Override
            public Expr visit(Func x) throws Err {
                throw new ErrorFatal("Visiting Func isn't supported!");
            }

            @Override
            public Expr visit(Assert x) throws Err {
                throw new ErrorFatal("Visiting Assert isn't supported!");
            }

            @Override
            public Expr visit(Macro macro) throws Err {
                throw new ErrorFatal("Visiting Macro isn't supported!");
            }
        });
    }

}
