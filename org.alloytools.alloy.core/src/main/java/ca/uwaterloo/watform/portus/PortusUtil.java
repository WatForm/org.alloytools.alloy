package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
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
     * Get the list of Fortress sorts that correspond to the sigs making up the
     * expr's type. This corresponds to the `sort` function in KT.
     *
     * Note that we <b>do not</b> yet support types with multiple ProductTypes,
     * that is, types that are the union of multiple products of top-level sigs.
     * (For example, we don't support `A + B` where A and B are distinct sigs.)
     *
     * @return A list of sorts corresponding to expr's type.
     * @throws ErrorType If expr's type has more than one ProductType,
     *  or if some sigs don't have mappings.
     */
    public static List<Sort> getSorts(Expr expr, TranslationContext context) {
        Type type = expr.type();
        if (type.size() != 1) {
            throw new ErrorType("Portus does not support types with more than one ProductType!");
        }
        Type.ProductType product = type.iterator().next();

        // get the sort from the context for each sig in the product type
        List<Sort> sorts = new ArrayList<>();
        for (int sigIdx = 0; sigIdx < product.arity(); sigIdx++) {
            Sig.PrimSig sig = product.get(sigIdx);
            Sort sort = context.getSigSort(sig);
            if (sort == null) {
                throw new ErrorType("Sig " + sig + " used in ProductType has no Sort mapping.");
            }
            sorts.add(sort);
        }

        return sorts;
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
            conjuncts.add(Term.mkAnd(a.get(i).variable(), b.get(i).variable()));
        }
        return Term.mkAnd(conjuncts);
    }

}
