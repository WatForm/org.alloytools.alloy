package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.operations.Substituter;
import fortress.operations.TermOps;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Tests Alloy expressions for a subset of alpha equivalence (wrt Alloy variables only).
 * If test(e1, e2) is true, then e1 and e2 are alpha-equivalent including free variables, but not necessarily the other
 * way around.
 * The closer this is to true alpha equivalence, the better ExprCache works.
 */
class PseudoAlphaEquivalence {

    /**
     * Test if e1 and e2 are alpha equivalent.
     * WARNING: e1 and e2 are assumed to have already been run through {@link PortusUtil#expandLets}!
     * Free variables are passed in independently to enable caching them.
     */
    public static boolean test(
            Expr e1, Expr e2, List<AnnotatedVar> e1FreeVars, List<AnnotatedVar> e2FreeVars,
            VarMappingContext e1Context, VarMappingContext e2Context) {
        // Free variables must match in number and sort
        if (e1FreeVars.size() != e2FreeVars.size()) return false;
        List<Sort> e1FVSorts = e1FreeVars.stream().map(AnnotatedVar::sort).collect(Collectors.toList());
        List<Sort> e2FVSorts = e2FreeVars.stream().map(AnnotatedVar::sort).collect(Collectors.toList());
        if (!e1FVSorts.equals(e2FVSorts)) return false;

        Map<String, String> e1ToE2AlphaMap = new HashMap<>();
        for (int i = 0; i < e1FreeVars.size(); i++) {
            e1ToE2AlphaMap.put(e1FreeVars.get(i).name(), e2FreeVars.get(i).name());
        }

        return new Visitor(e1ToE2AlphaMap, e2, e1Context, e2Context).visitThis(e1);
    }

    private static class Visitor extends FortressVisitReturn<Boolean> {

        // value irrelevant, this is just to keep track of which vars are bound
        private final Env<String, Boolean> boundVarsSelf = new Env<>();
        private final Env<String, Boolean> boundVarsOther = new Env<>();

        private final Map<String, String> alphaMap; // this to other
        private Expr other;

        // For mapping Alloy variables to Fortress variables so we can alpha-map them
        private final VarMappingContext selfContext;
        private final VarMappingContext otherContext;

        public Visitor(Map<String, String> alphaMap, Expr other,
                       VarMappingContext selfContext, VarMappingContext otherContext) {
            this.alphaMap = alphaMap;
            this.other = PortusUtil.stripPortusNoops(other);
            this.selfContext = selfContext;
            this.otherContext = otherContext;
        }

        private boolean recurse(Expr newX, Expr newOther) {
            // this is very ugly...
            Expr oldOther = other;
            other = PortusUtil.stripPortusNoops(newOther);
            try {
                return visitThis(newX);
            } finally {
                other = oldOther;
            }
        }

        private boolean recurseList(List<? extends Expr> xList, List<? extends Expr> otherList) {
            if (xList.size() != otherList.size()) return false;
            for (int i = 0; i < xList.size(); i++) {
                if (!recurse(xList.get(i), otherList.get(i))) {
                    return false;
                }
            }
            return true;
        }

        private boolean areTermsAlphaEquiv(AnnotatedTerm x, AnnotatedTerm other) {
            // are the terms the same, after substituting with the alpha map?
            if (!x.getSort().equals(other.getSort())) return false;

            // Forbid all names in x and other so any generated bound var names are fresh wrt both terms
            NameGenerator nameGenerator = new SanitizingNameGenerator();
            //noinspection unchecked
            Set<String> xSymbols = CollectionConverters.<String>asJava(
                    TermOps.wrapTerm(x.getTerm()).allSymbols());
            for (String name : xSymbols) {
                nameGenerator.forbidName(name);
            }
            //noinspection unchecked
            Set<String> otherSymbols = CollectionConverters.<String>asJava(
                    TermOps.wrapTerm(other.getTerm()).allSymbols());
            for (String name : otherSymbols) {
                nameGenerator.forbidName(name);
            }

            // We want to simulate substituting simultaneously, but Substituter only substitutes sequentially.
            // So substitute from keys to some fresh variables, then those fresh variables to the values.
            Map<String, String> keysToFresh = new HashMap<>();
            Map<String, String> freshToValues = new HashMap<>();
            for (String key : alphaMap.keySet()) {
                String value = alphaMap.get(key);
                String freshName = nameGenerator.freshName("__IF_YOU_SEE_THIS_THERES_A_BUG");
                keysToFresh.put(key, freshName);
                freshToValues.put(freshName, value);
            }

            // Substitute to other safely, in two stages as described above.
            // Due to alpha-renaming to avoid var capture we might miss a few alpha-equivalent terms, but that's okay.
            // We can't ignore variable capture due to the following example:
            //  x := a && all b | p(a)
            //  y := b && all b | p(b)
            // alphaMap: a->b
            // then sub(x) := b && all b | p(b) would wrongly match due to variable capture if we ignored var capture
            Term substitutedX = x.getTerm();
            for (String key : keysToFresh.keySet()) {
                String freshName = keysToFresh.get(key);
                substitutedX = Substituter.apply(Term.mkVar(key), Term.mkVar(freshName), substitutedX, nameGenerator);
            }
            for (String freshName : freshToValues.keySet()) {
                String value = freshToValues.get(freshName);
                substitutedX = Substituter.apply(Term.mkVar(freshName), Term.mkVar(value), substitutedX, nameGenerator);
            }

            // Now they should match perfectly!
            return substitutedX.equals(other.getTerm());
        }

        @Override
        public Boolean visit(ExprElementOf x) throws Err {
            if (!(other instanceof ExprElementOf)) return false;
            ExprElementOf otherElementOf = (ExprElementOf) other;
            // The terms must each be alpha-equivalent under the alpha map
            if (x.tuple.size() != otherElementOf.tuple.size()) return false;
            for (int i = 0; i < x.tuple.size(); i++) {
                if (!areTermsAlphaEquiv(x.tuple.getAnnotatedTerm(i), otherElementOf.tuple.getAnnotatedTerm(i))) {
                    return false;
                }
            }
            return recurse(x.sub, otherElementOf.sub);
        }

        @Override
        public Boolean visit(ExprList x) throws Err {
            if (!(other instanceof ExprList)) return false;
            ExprList otherList = (ExprList) other;
            if (x.op != otherList.op) return false;
            return recurseList(x.args, otherList.args);
        }

        @Override
        public Boolean visit(ExprCall x) throws Err {
            // Specifically do not run the fun/pred name through the alpha map!
            // That would be semantically wrong and also break ExprDefnOptTranslator
            if (!(other instanceof ExprCall)) return false;
            ExprCall otherCall = (ExprCall) other;
            // assume labels are unique
            if (!x.fun.label.equals(otherCall.fun.label)) return false;
            return recurseList(x.args, otherCall.args);
        }

        @Override
        public Boolean visit(ExprConstant x) throws Err {
            if (!(other instanceof ExprConstant)) return false;
            ExprConstant otherConst = (ExprConstant) other;
            return x.op == otherConst.op && x.num == otherConst.num && x.string.equals(otherConst.string);
        }

        @Override
        public Boolean visit(ExprITE x) throws Err {
            if (!(other instanceof ExprITE)) return false;
            ExprITE otherITE = (ExprITE) other;
            return recurse(x.cond, otherITE.cond) && recurse(x.left, otherITE.left) && recurse(x.right, otherITE.right);
        }

        @Override
        public Boolean visit(ExprLet x) throws Err {
            throw new ErrorFatal("Internal Portus error: ExprLets should be eliminated here!");
        }

        @Override
        public Boolean visit(ExprQt x) throws Err {
            // Don't bother checking for bound var alpha-equivalence
            // (e.g. all x: A | f and all y: A | f will compare different)
            if (!(other instanceof ExprQt)) return false;
            ExprQt otherQt = (ExprQt) other;
            if (x.op != otherQt.op) return false;
            if (x.decls.size() != otherQt.decls.size()) return false;

            List<String> newBoundSelf = new ArrayList<>();
            List<String> newBoundOther = new ArrayList<>();

            for (int i = 0; i < x.decls.size(); i++) {
                Decl decl1 = x.decls.get(i);
                Decl decl2 = otherQt.decls.get(i);
                if (!Objects.equals(decl1.disjoint, decl2.disjoint)) return false;
                if (!Objects.equals(decl1.disjoint2, decl2.disjoint2)) return false;
                if (!recurseList(decl1.names, decl2.names)) {
                    return false;
                }
                if (!recurse(decl1.expr, decl2.expr)) {
                    return false;
                }
                for (int j = 0; j < decl1.names.size(); j++) {
                    newBoundSelf.add(decl1.names.get(j).label);
                    newBoundOther.add(decl2.names.get(j).label);
                }
            }

            for (String name : newBoundSelf) {
                boundVarsSelf.put(name, true);
            }
            for (String name : newBoundOther) {
                boundVarsOther.put(name, true);
            }

            try {
                return recurse(x.sub, otherQt.sub);
            } finally {
                for (int i = newBoundSelf.size() - 1; i >= 0; i--) {
                    boundVarsSelf.remove(newBoundSelf.get(i));
                }
                for (int i = newBoundOther.size() - 1; i >= 0; i--) {
                    boundVarsOther.remove(newBoundOther.get(i));
                }
            }
        }

        @Override
        public Boolean visit(ExprUnary x) throws Err {
            if (x.op == ExprUnary.Op.NOOP) {
                return visitThis(x.sub); // ignore noops
            }
            if (!(other instanceof ExprUnary)) return false;
            ExprUnary otherUnary = (ExprUnary) other;
            if (x.op != otherUnary.op) return false;
            return recurse(x.sub, otherUnary.sub);
        }

        @Override
        public Boolean visit(ExprBinary x) throws Err {
            if (!(other instanceof ExprBinary)) return false;
            ExprBinary otherBinary = (ExprBinary) other;
            if (x.op != otherBinary.op) return false;
            // require same order
            return recurse(x.left, otherBinary.left) && recurse(x.right, otherBinary.right);
        }

        @Override
        public Boolean visit(ExprVar x) throws Err {
            // Lets are already expanded, so no need to handle them
            if (!(other instanceof ExprVar)) return false;
            ExprVar otherVar = (ExprVar) other;

            // Don't bother trying to handle bound variable alpha-equivalences
            boolean xBound = boundVarsSelf.has(x.label);
            boolean otherBound = boundVarsOther.has(otherVar.label);
            if (xBound || otherBound) {
                // both must be bound and have equal labels - require exact match
                return xBound && otherBound && x.label.equals(otherVar.label);
            }

            // Neither bound: if in the context, must map to same term after apply alpha map
            boolean hasX = selfContext.hasTermMapping(x.label);
            boolean hasOther = otherContext.hasTermMapping(otherVar.label);
            if (hasX || hasOther) {
                if (!(hasX && hasOther)) return false;
                AnnotatedTerm xTerm = selfContext.getTermMapping(x.label);
                AnnotatedTerm yTerm = otherContext.getTermMapping(otherVar.label);
                assert xTerm != null && yTerm != null;
                return areTermsAlphaEquiv(xTerm, yTerm);
            }

            // Otherwise assume they're constants: require exact match
            return x.label.equals(otherVar.label);
        }

        @Override
        public Boolean visit(Sig x) throws Err {
            // Must be the same sig name
            if (!(other instanceof Sig)) return false;
            Sig otherSig = (Sig) other;
            return x.label.equals(otherSig.label);
        }

        @Override
        public Boolean visit(Sig.Field x) throws Err {
            // Must be the same field name
            if (!(other instanceof Sig.Field)) return false;
            Sig.Field otherField = (Sig.Field) other;
            return x.label.equals(otherField.label);
        }

        @Override
        public Boolean visit(Func x) throws Err {
            throw new ErrorNoPortusSupport("Visiting Func is not supported");
        }

        @Override
        public Boolean visit(Assert x) throws Err {
            throw new ErrorNoPortusSupport("Visiting Assert is not supported");
        }

        @Override
        public Boolean visit(Macro macro) throws Err {
            throw new ErrorNoPortusSupport("Visiting Macro is not supported");
        }

    }

}
