package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Assert;
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
import fortress.msfol.AnnotatedVar;
import org.hamcrest.Description;
import org.hamcrest.TypeSafeMatcher;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Provides a Hamcrest matcher for matching Alloy expressions.
 * Tests alpha-equivalence between two expressions.
 * TODO: test this class (even though it's for test support...)
 * TODO: also maybe refactor to use Env
 */
public class AlloyASTMatcher extends TypeSafeMatcher<Expr> {

    private final Expr base;

    public AlloyASTMatcher(Expr base) {
        this.base = base;
    }

    public static AlloyASTMatcher isAlphaEquivalent(Expr base) {
        return new AlloyASTMatcher(base);
    }

    @Override
    protected boolean matchesSafely(Expr expr) {
        return AlphaEquivalenceTester.areAlphaEquivalent(base, expr);
    }

    private static class AlphaEquivalenceTester extends FortressVisitReturn<Boolean> {

        // map of alpha-equivalent bound/free variables from a to b
        private Map<String, String> boundVarMap = new HashMap<>();
        private final Map<String, String> freeVarMap = new HashMap<>();
        // for Fortress variables as used in ExprElementOf
        private final Map<String, String> fortressVarMap = new HashMap<>();

        // variables that are currently bound in each expression
        private Set<String> boundVarsA = new HashSet<>();
        private Set<String> boundVarsB = new HashSet<>();

        private Expr testing;

        /**
         * Test whether `a` and `b` are alpha-equivalent.
         */
        public static boolean areAlphaEquivalent(Expr a, Expr b) {
            AlphaEquivalenceTester tester = new AlphaEquivalenceTester();
            return tester.equivalent(a, b);
        }

        private AlphaEquivalenceTester() {}

        private Expr stripNoop(Expr expr) {
            // strip NOOP, CAST2INT, CAST2SIGINT
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

        private boolean equivalent(Expr a, Expr b) {
            a = stripNoop(a);
            b = stripNoop(b);

            // hacky workaround to pass through multiple exprs
            Expr prev = testing;
            testing = b;
            boolean result = visitThis(a);
            testing = prev;
            return result;
        }

        @Override
        public Boolean visit(ExprBinary x) throws Err {
            if (!(testing instanceof ExprBinary)) return false;
            ExprBinary y = (ExprBinary) testing;
            return x.op == y.op
                    && equivalent(x.left, y.left)
                    && equivalent(x.right, y.right);
        }

        @Override
        public Boolean visit(ExprList x) throws Err {
            if (!(testing instanceof ExprList)) return false;
            ExprList y = (ExprList) testing;
            // require the args to be in the same order for now
            return x.op == y.op && x.args.size() == y.args.size()
                    && IntStream.range(0, x.args.size()).allMatch(
                            i -> equivalent(x.args.get(i), y.args.get(i)));
        }

        @Override
        public Boolean visit(ExprCall x) throws Err {
            throw new UnsupportedOperationException(
                    "Alpha-equivalence is not yet supported for ExprCall");
        }

        @Override
        public Boolean visit(ExprConstant x) throws Err {
            if (!(testing instanceof ExprConstant)) return false;
            ExprConstant y = (ExprConstant) testing;
            if (x.op != y.op) return false;
            switch (x.op) {
                case NUMBER:
                    return x.num == y.num;
                case STRING:
                    return x.string.equals(y.string);
                default:
                    // others have only one possible value
                    return true;
            }
        }

        @Override
        public Boolean visit(ExprITE x) throws Err {
            if (!(testing instanceof ExprITE)) return false;
            ExprITE y = (ExprITE) testing;
            return equivalent(x.cond, y.cond)
                    && equivalent(x.left, y.left)
                    && equivalent(x.right, y.right);
        }

        @Override
        public Boolean visit(ExprLet x) throws Err {
            if (!(testing instanceof ExprLet)) return false;
            ExprLet y = (ExprLet) testing;
            return equivalent(x.var, y.var)
                    && equivalent(x.expr, y.expr)
                    && equivalent(x.sub, y.sub);
        }

        @Override
        public Boolean visit(ExprQt x) throws Err {
            if (!(testing instanceof ExprQt)) return false;
            ExprQt y = (ExprQt) testing;
            if (x.op != y.op) return false;
            if (x.decls.size() != y.decls.size()) return false;

            // deal with redefined variables by copying and restoring the map + sets
            Map<String, String> savedVarMap = new HashMap<>(boundVarMap);
            Set<String> savedBoundVarsA = new HashSet<>(boundVarsA);
            Set<String> savedBoundVarsB = new HashSet<>(boundVarsB);

            // assume the decls are in the same order, map them to each other
            for (int i = 0; i < x.decls.size(); i++) {
                // the decl expressions must be equivalent too
                if (!equivalent(x.decls.get(i).expr, y.decls.get(i).expr)) return false;

                // map all the names to each other
                List<? extends ExprHasName> xNames = x.decls.get(i).names;
                List<? extends ExprHasName> yNames = y.decls.get(i).names;
                if (xNames.size() != yNames.size()) return false;
                for (int j = 0; j < xNames.size(); j++) {
                    boundVarMap.put(xNames.get(j).label, yNames.get(j).label);
                    boundVarsA.add(xNames.get(j).label);
                    boundVarsB.add(yNames.get(j).label);
                }
            }

            boolean result = equivalent(x.sub, y.sub);
            boundVarMap = savedVarMap; // restore to deal with redefined variables
            boundVarsA = savedBoundVarsA;
            boundVarsB = savedBoundVarsB;
            return result;
        }

        @Override
        public Boolean visit(ExprUnary x) throws Err {
            if (!(testing instanceof ExprUnary)) return false;
            ExprUnary y = (ExprUnary) testing;
            return x.op == y.op && equivalent(x.sub, y.sub);
        }

        @Override
        public Boolean visit(ExprVar x) throws Err {
            if (!(testing instanceof ExprVar)) return false;
            ExprVar y = (ExprVar) testing;
            return visitVariableName(x.label, y.label);
        }

        @Override
        public Boolean visit(ExprElementOf x) throws Err {
            if (!(testing instanceof ExprElementOf)) return false;
            ExprElementOf y = (ExprElementOf) testing;
            if (x.tuple.size() != y.tuple.size()) return false;

            // check that each Fortress term (and its sort) is alpha-equivalent
            for (int i = 0; i < x.tuple.size(); i++) {
                AnnotatedTerm xTerm = x.tuple.getAnnotatedTerm(i);
                AnnotatedTerm yTerm = y.tuple.getAnnotatedTerm(i);
                // This definitely isn't the best way to do it, but should be good enough since we also check free vars
                if (!checkMapping(xTerm.getTerm().toString(), yTerm.getTerm().toString(), fortressVarMap)
                    || !checkMapping(xTerm.getSort().name(), yTerm.getSort().name(), fortressVarMap)) {
                    return false;
                }
                if (xTerm.getFreeVars().size() != yTerm.getFreeVars().size()) {
                    return false;
                }
                Comparator<AnnotatedVar> varSorter = Comparator.comparing(AnnotatedVar::toString);
                List<AnnotatedVar> xFreeVars = xTerm.getFreeVars().stream()
                        .sorted(varSorter)
                        .collect(Collectors.toList());
                List<AnnotatedVar> yFreeVars = yTerm.getFreeVars().stream()
                        .sorted(varSorter)
                        .collect(Collectors.toList());
                for (int j = 0; j < xFreeVars.size(); j++) {
                    if (!checkMapping(xFreeVars.get(j).name(), yFreeVars.get(j).name(), fortressVarMap)
                        || !checkMapping(
                                xFreeVars.get(j).sort().name(), yFreeVars.get(j).sort().name(), fortressVarMap)) {
                        return false;
                    }
                }
            }

            return equivalent(x.sub, y.sub);
        }

        @Override
        public Boolean visit(Sig x) throws Err {
            if (!(testing instanceof Sig)) return false;
            Sig y = (Sig) testing;

            // assume we go through sigs in the same order, make sure everything is the same
            if (x.isTopLevel() != y.isTopLevel()
                || x.builtin != y.builtin
                || (x.isAbstract == null) != (y.isAbstract == null)
                || (x.isEnum == null) != (y.isEnum == null)
                || (x.isLone == null) != (y.isLone == null)
                || (x.isOne == null) != (y.isOne == null)
                || (x.isSome == null) != (y.isSome == null)
                || (x.isSubset == null) != (y.isSubset == null)
                || (x.isSubsig == null) != (y.isSubsig == null)
                || (x.isVariable == null) != (y.isVariable == null)
                || (x instanceof Sig.PrimSig) != (y instanceof Sig.PrimSig)) {
                return false;
            }

            // map the sig names to each other
            visitVariableName(x.label, y.label);

            // check subclass-specific fields, like children and parents
            if (x instanceof Sig.PrimSig) {
                Sig.PrimSig primX = (Sig.PrimSig) x;
                Sig.PrimSig primY = (Sig.PrimSig) y;
                if (x != Sig.UNIV) { // Alloy chokes enumerating children of univ
                    // make sure the children are the same - assume we go through them in the same order
                    return areListsEquivalent(primX.children(), primY.children());
                }
            } else {
                Sig.SubsetSig subsetX = (Sig.SubsetSig) x;
                Sig.SubsetSig subsetY = (Sig.SubsetSig) y;
                if (subsetX.parents.size() != subsetY.parents.size()) return false;

                // make sure parents are mapped to each other
                // we can't just call equivalent() because we should have already mapped the parents
                // if the parents aren't mapped, assume we're translating only the subset sigs for efficiency and say ok
                for (int i = 0; i < subsetX.parents.size(); i++) {
                    String parentXLabel = subsetX.parents.get(i).label;
                    String parentYLabel = subsetY.parents.get(i).label;
                    if (!Objects.equals(freeVarMap.get(parentXLabel), freeVarMap.get(parentYLabel))) {
                        return false;
                    }
                }
            }

            // to avoid infinite recursion, don't bother checking the fields and facts
            return true;
        }

        @Override
        public Boolean visit(Sig.Field x) throws Err {
            if (!(testing instanceof Sig.Field)) return false;
            Sig.Field y = (Sig.Field) testing;
            return equivalent(x.decl().expr, y.decl().expr)
                    && visitVariableName(x.label, y.label);
        }

        @Override
        public Boolean visit(Func x) throws Err {
            throw new UnsupportedOperationException(
                    "Alpha-equivalence is not yet supported for Func");
        }

        @Override
        public Boolean visit(Assert x) throws Err {
            throw new UnsupportedOperationException(
                    "Alpha-equivalence is not yet supported for Assert");
        }

        @Override
        public Boolean visit(Macro macro) throws Err {
            throw new UnsupportedOperationException(
                    "Alpha-equivalence is not yet supported for Macro");
        }

        // compare two variable names for alpha-equivalence and deal with side effects
        private boolean visitVariableName(String x, String y) {
            // if either are bound, both must be bound
            if (boundVarsA.contains(x) != boundVarsB.contains(y)) {
                return false;
            }

            // what map are they in?
            Map<String, String> map = boundVarsA.contains(x) ? boundVarMap : freeVarMap;
            return checkMapping(x, y, map);
        }

        // compare x and y for alpha-equivalence using the map
        private boolean checkMapping(String x, String y, Map<String, String> map) {
            // if mapped, they must be mapped to each other
            if (map.containsKey(x)) {
                return map.get(x).equals(y);
            } else if (map.containsValue(y)) {
                // x isn't mapped, so not mapped to each other
                return false;
            } else {
                // they must be free variables since they aren't mapped, so add a mapping
                map.put(x, y);
                return true;
            }
        }

        private boolean areListsEquivalent(SafeList<? extends Expr> a, SafeList<? extends Expr> b) {
            if (a.size() != b.size()) return false;
            for (int i = 0; i < a.size(); i++) {
                if (!equivalent(a.get(i), b.get(i))) {
                    return false;
                }
            }
            return true;
        }

    }

    @Override
    public void describeTo(Description description) {
        description.appendText("alpha-equivalent to <");
        StringBuilder builder = new StringBuilder();
        base.toString(builder, -1);
        description.appendText(builder.toString()).appendText(">");
    }

}
