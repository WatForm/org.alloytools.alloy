package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Term;
import fortress.msfol.Var;
import fortress.operations.Substituter;
import scala.collection.immutable.HashSet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * General-purpose utility functions used in Portus.
 */
final class PortusUtil {

    private PortusUtil() {}

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
        @SuppressWarnings("unchecked") // IntelliJ false positive
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

}
