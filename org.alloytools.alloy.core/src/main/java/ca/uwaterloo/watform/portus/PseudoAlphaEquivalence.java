package ca.uwaterloo.watform.portus;

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
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
    public static boolean test(Expr e1, Expr e2, List<AnnotatedVar> e1FreeVars, List<AnnotatedVar> e2FreeVars) {
        // Free variables must match in number and sort
        if (e1FreeVars.size() != e2FreeVars.size()) return false;
        List<Sort> e1FVSorts = e1FreeVars.stream().map(AnnotatedVar::sort).collect(Collectors.toList());
        List<Sort> e2FVSorts = e2FreeVars.stream().map(AnnotatedVar::sort).collect(Collectors.toList());
        if (!e1FVSorts.equals(e2FVSorts)) return false;

        Map<String, String> e1ToE2AlphaMap = new HashMap<>();
        for (int i = 0; i < e1FreeVars.size(); i++) {
            e1ToE2AlphaMap.put(e1FreeVars.get(i).name(), e2FreeVars.get(i).name());
        }

        return new Visitor(e1ToE2AlphaMap, e2).visitThis(e1);
    }

    private static class Visitor extends FortressVisitReturn<Boolean> {

        private final Map<String, String> alphaMap; // this to other
        private Expr other;

        public Visitor(Map<String, String> alphaMap, Expr other) {
            this.alphaMap = alphaMap;
            this.other = PortusUtil.stripPortusNoops(other);
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

        @Override
        public Boolean visit(ExprElementOf x) throws Err {
            if (!(other instanceof ExprElementOf)) return false;
            ExprElementOf otherElementOf = (ExprElementOf) other;
            // Don't check the variable names of the tuples at all - it's fine
            return x.tuple.getSorts().equals(otherElementOf.tuple.getSorts()) && recurse(x.sub, otherElementOf.sub);
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
            }
            return recurse(x.sub, otherQt.sub);
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

            // Must be the same variable name after application of the alpha map
            // Don't bother trying to handle bound variable alpha-equivalences
            String label;
            if (alphaMap.containsKey(x.label)) {
                label = alphaMap.get(x.label);
            } else {
                label = x.label;
            }
            return label.equals(otherVar.label);
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
