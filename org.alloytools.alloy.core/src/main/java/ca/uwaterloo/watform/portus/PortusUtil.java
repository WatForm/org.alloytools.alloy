package ca.uwaterloo.watform.portus;

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
