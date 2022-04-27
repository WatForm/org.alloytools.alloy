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
import java.util.List;

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
     * Return the unary multiplicity operator corresponding to "M" in "M->N", or SETOF if
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
                return ExprUnary.Op.ONEOF;
            case LONE_ARROW_ANY:
            case LONE_ARROW_ONE:
            case LONE_ARROW_LONE:
            case LONE_ARROW_SOME:
                return ExprUnary.Op.LONEOF;
            case SOME_ARROW_ANY:
            case SOME_ARROW_ONE:
            case SOME_ARROW_LONE:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOMEOF;
            default:
                return ExprUnary.Op.SETOF;
        }
    }

    /**
     * Return the unary multiplicity operator corresponding to "N" in "M->N", or SETOF if
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
                return ExprUnary.Op.ONEOF;
            case ANY_ARROW_LONE:
            case ONE_ARROW_LONE:
            case LONE_ARROW_LONE:
            case SOME_ARROW_LONE:
                return ExprUnary.Op.LONEOF;
            case ANY_ARROW_SOME:
            case ONE_ARROW_SOME:
            case LONE_ARROW_SOME:
            case SOME_ARROW_SOME:
                return ExprUnary.Op.SOMEOF;
            default:
                return ExprUnary.Op.SETOF;
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
    public static Term substitute(List<AnnotatedVar> a, List<AnnotatedVar> b, Term term) {
        if (a.size() != b.size()) {
            throw new IllegalArgumentException("a and b must have same size");
        }

        // TODO: can we use FastSubstituter in some cases?
        NameGenerator nameGen = new IntSuffixNameGenerator(new HashSet<>(), 0);
        for (int i = 0; i < a.size(); i++) {
            Var v1 = a.get(i).variable();
            Var v2 = b.get(i).variable();
            term = Substituter.apply(v1, v2, term, nameGen);
        }
        return term;
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

}
