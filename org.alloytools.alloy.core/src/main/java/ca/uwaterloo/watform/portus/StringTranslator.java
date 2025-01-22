package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.DomainElement;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.*;

/**
 * Handles translating strings. Should always be enabled.
 */
final class StringTranslator extends AbstractTranslator implements ScalarCaster, StringDecoder {

    private final ModelInfo modelInfo;
    private final SortPolicy sortPolicy;

    private final Map<String, DomainElement> stringConstsToDEs = new HashMap<>();
    private final Map<DomainElement, String> desToStringConsts = new HashMap<>();

    public StringTranslator(Translator topLevel, ModelInfo modelInfo, SortPolicy sortPolicy) {
        super(topLevel);
        this.modelInfo = modelInfo;
        this.sortPolicy = sortPolicy;
    }

    @Override
    public Term translate(Sig sig, TranslationContext context) {
        if (!sig.equals(Sig.STRING)) return null;

        if (modelInfo.numStringConstants() == 0) {
            // there are no strings in the model: do nothing and avoid any extra cost
            return Term.mkTop();
        }

        // Set up the map from string constants to DEs
        Sort stringSort = sortPolicy.getStringSort();
        Pair<Integer, Integer> stringDERange = context.rangeAssigner.getDomainElementRange(Sig.STRING);
        if (stringDERange.b - stringDERange.a + 1 != modelInfo.numStringConstants()) {
            throw new ErrorFatal("Portus bug: String was not assigned the correct number of domain elements");
        }

        Iterator<String> stringIterator = modelInfo.getStringConstants().iterator();
        for (int deIdx = stringDERange.a; deIdx <= stringDERange.b; deIdx++) {
            String stringConst = stringIterator.next();
            DomainElement de = Term.mkDomainElement(deIdx, stringSort);
            stringConstsToDEs.put(stringConst, de);
            desToStringConsts.put(de, stringConst);
        }

        return Term.mkTop();
    }

    private DomainElement getDEForString(String stringConstant) {
        DomainElement de = stringConstsToDEs.get(stringConstant);
        if (de == null) {
            throw new ErrorFatal("Unknown string constant: \"" + stringConstant + "\"");
        }
        return de;
    }

    @Override
    public Term translate(TermTuple tuple, ExprConstant expr, TranslationContext context) {
        if (expr.op != ExprConstant.Op.STRING) return null;
        if (tuple.size() != 1) {
            throw new ErrorFatal("String constants have arity 1!");
        }

        Sort stringSort = sortPolicy.getStringSort();
        if (!tuple.getSort(0).equals(stringSort)) {
            return Term.mkBottom(); // short-circuit
        }
        return Term.mkEq(tuple.getTerm(0), getDEForString(expr.string));
    }

    @Override
    public Term translate(AnnotatedTerm var, Sig sig, TranslationContext context) {
        if (!sig.equals(Sig.STRING)) return null;

        if (modelInfo.numStringConstants() == 0) {
            return Term.mkBottom(); // no strings in the model: short-circuit
        }
        if (!var.getSort().equals(sortPolicy.getStringSort())) {
            return Term.mkBottom(); // short-circuit
        }

        // Translate "var \in String": just an OR with the DEs
        List<Term> disjuncts = new ArrayList<>();
        for (DomainElement de : stringConstsToDEs.values()) {
            disjuncts.add(Term.mkEq(var.getTerm(), de));
        }
        return Term.mkOr(disjuncts);
    }

    @Override
    public Scalar castToScalar(Expr expr, TranslationContext context) {
        if (!(expr instanceof ExprConstant)) return null;
        ExprConstant exprConst = (ExprConstant) expr;
        if (exprConst.op != ExprConstant.Op.STRING) return null;

        return new Scalar(sortPolicy.getStringSort(), getDEForString(exprConst.string), Term.mkTop());
    }

    @Override
    public String decode(DomainElement de) {
        return desToStringConsts.get(de);
    }

    @Override
    public String name() {
        return "String";
    }

}
