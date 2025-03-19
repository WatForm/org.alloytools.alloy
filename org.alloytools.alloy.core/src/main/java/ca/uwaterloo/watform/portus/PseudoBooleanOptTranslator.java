package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.Macro;
import fortress.msfol.Sort;
import fortress.msfol.Term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

class PseudoBooleanOptTranslator extends AbstractTranslator {

    private final SortPolicy sortPolicy;

    public PseudoBooleanOptTranslator(Translator topLevel, SortPolicy sortPolicy) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
    }

    @Override
    public String name() {
        return "Pseudo-Boolean Optimization";
    }

    @Override
    public Term translate(ExprBinary expr, TranslationContext context) {
        switch (expr.op) {
            case EQUALS:
            case NOT_EQUALS:
            case LT:
            case LTE:
            case GT:
            case GTE:
            case NOT_LT:
            case NOT_LTE:
            case NOT_GT:
            case NOT_GTE:
                return translateComparison(expr.op, expr.left, expr.right, context);
            default:
                return null;
        }
    }

    private Term translateComparison(ExprBinary.Op op, Expr left, Expr right, TranslationContext context) {
        PbVisitor visitor = new PbVisitor(context, sortPolicy);
        PbExpr leftPb = visitor.visitThis(left);
        if (leftPb == null) return null;
        PbExpr rightPb = visitor.visitThis(right);
        if (rightPb == null) return null;

        PbExpr difference = PbExpr.minus(leftPb, rightPb);

        switch (op) {
            case EQUALS:
                return difference.makeEqZero();
            case NOT_EQUALS:
                return Term.mkNot(difference.makeEqZero());
            case LTE:
            case NOT_GT:
                return difference.makeLeZero();
            case GTE:
            case NOT_LT:
                return difference.makeGeZero();
            case LT:
            case NOT_GTE:
                return difference.makeLtZero();
            case GT:
            case NOT_LTE:
                return difference.makeGtZero();
            default:
                return null;
        }
    }

    // represents "coeffs . terms + constant"
    private static class PbExpr {

        private final List<Term> terms;
        private final List<Integer> coeffs;
        private final int constant;

        public PbExpr(List<Term> terms, List<Integer> coeffs, int constant) {
            if (terms.size() != coeffs.size()) throw new IllegalArgumentException();
            this.terms = terms;
            this.coeffs = coeffs;
            this.constant = constant;
        }

        public PbExpr(List<Term> terms, List<Integer> coeffs) {
            this(terms, coeffs, 0);
        }

        public PbExpr(int constant) {
            this(Collections.emptyList(), Collections.emptyList(), constant);
        }

        public Term makeEqZero() {
            return makeSmtlibPred("pbeq", -constant);
        }

        public Term makeLeZero() {
            return makeSmtlibPred("pble", -constant);
        }

        public Term makeGeZero() {
            return makeSmtlibPred("pbge", -constant);
        }

        public Term makeLtZero() {
            return new PbExpr(terms, coeffs, constant+1).makeLeZero();
        }

        public Term makeGtZero() {
            return new PbExpr(terms, coeffs, constant-1).makeGeZero();
        }

        private Term makeSmtlibPred(String pred, int k) {
            StringBuilder smtlib = new StringBuilder("(_ " + pred + " " + k);
            for (int coeff : coeffs) {
                smtlib.append(" ");
                smtlib.append(coeff);
            }
            smtlib.append(")");
            return Term.mkCustomPred(smtlib.toString(), terms);
        }

        public static PbExpr negate(PbExpr pb) {
            if (pb == null) return null;
            return new PbExpr(pb.terms, pb.coeffs.stream().map(coeff -> -coeff).collect(Collectors.toList()),
                    -pb.constant);
        }

        // TODO try to merge on same terms?

        public static PbExpr plus(PbExpr pb1, PbExpr pb2) {
            if (pb1 == null || pb2 == null) return null;
            return new PbExpr(
                    SetOps.concatenate(pb1.terms, pb2.terms),
                    SetOps.concatenate(pb1.coeffs, pb2.coeffs),
                    pb1.constant + pb2.constant);
        }

        public static PbExpr minus(PbExpr pb1, PbExpr pb2) {
            return plus(pb1, negate(pb2));
        }

        public static PbExpr timesCondition(Term condition, PbExpr pb) {
            // AND condition with all terms, map constant -> coeff of condition
            if (pb == null) return null;

            List<Term> newTerms = new ArrayList<>(pb.terms.size() + 1);
            List<Integer> newCoeffs = new ArrayList<>(pb.coeffs);

            for (int i = 0; i < pb.terms.size(); i++) {
                newTerms.add(Term.mkAnd(condition, pb.terms.get(i)));
            }
            newTerms.add(condition);
            newCoeffs.add(pb.constant);

            return new PbExpr(newTerms, newCoeffs);
        }

        public static PbExpr ite(Term condition, PbExpr ifTrue, PbExpr ifFalse) {
            if (ifTrue == null || ifFalse == null) return null;

            // condition*ifTrue + (!condition)*ifFalse
            return plus(timesCondition(condition, ifTrue), timesCondition(Term.mkNot(condition), ifFalse));
        }

    }

    // Generate a PbExpr corresponding to an Alloy expression
    private class PbVisitor extends FortressVisitReturn<PbExpr> {

        // We never recurse into anything that would modify the context, so we can do this
        // TODO: expanding lets??
        private final TranslationContext context;
        private final SortPolicy sortPolicy;
        private final int bitwidth;

        public PbVisitor(TranslationContext context, SortPolicy sortPolicy) {
            this.context = context;
            this.sortPolicy = sortPolicy;
            this.bitwidth = context.getBitwidth();
        }

        @Override
        public PbExpr visit(ExprConstant x) throws Err {
            if (x.op == ExprConstant.Op.NUMBER) {
                return new PbExpr(x.num);
            } else if (x.op == ExprConstant.Op.MAX) {
                return new PbExpr(Util.max(bitwidth));
            } else if (x.op == ExprConstant.Op.MIN) {
                return new PbExpr(Util.min(bitwidth));
            } else {
                return null;
            }
        }

        @Override
        public PbExpr visit(ExprBinary x) throws Err {
            switch (x.op) {
                case IPLUS:
                    return PbExpr.plus(visitThis(x.left), visitThis(x.right));
                case IMINUS:
                    return PbExpr.minus(visitThis(x.left), visitThis(x.right));
                    // TODO: maybe experiment with mul (possibly div, rem?)
                default:
                    return null;
            }
        }

        @Override
        public PbExpr visit(ExprITE x) throws Err {
            PbExpr left = visitThis(x.left);
            PbExpr right = visitThis(x.right);
            if (left == null || right == null) return null;

            Term condition = recursivelyTranslate(x.cond, context);
            return PbExpr.ite(condition, left, right);
        }

        @Override
        public PbExpr visit(ExprUnary x) throws Err {
            switch (x.op) {
                case NOOP:
                case CAST2INT:
                case CAST2SIGINT:
                    return visitThis(x.sub);
                case CARDINALITY:
                    return visitCardinality(x.sub);
                default:
                    return null;
            }
        }

        private PbExpr visitCardinality(Expr sub) throws Err {
            SortResolvant resolvant = sortPolicy.getMinimalExprSorts(sub, context);
            if (resolvant.isNone()) {
                // Short-circuit: [[#none]] = 0
                return new PbExpr(0);
            }
            if (!resolvant.isDefinite()) {
                throw new ErrorNoPortusSupport("Argument of cardinality must have definite sorts!");
            }

            List<Sort> sorts = resolvant.getDefiniteSorts();
            List<Integer> scopes = sorts.stream().map(sortPolicy::getSortScope).collect(Collectors.toList());
            int totalAddends = scopes.stream().reduce(1, (x, y) -> x * y);

            List<Term> terms = new ArrayList<>(totalAddends);
            List<Integer> coeffs = new ArrayList<>(totalAddends);

            List<Integer> deNums = new ArrayList<>(sorts.size());
            for (int i = 0; i < sorts.size(); i++) {
                deNums.add(1);
            }

            boolean done;
            do {
                List<AnnotatedTerm> des = new ArrayList<>(sorts.size());
                for (int i = 0; i < sorts.size(); i++) {
                    des.add(new AnnotatedTerm(Term.mkDomainElement(deNums.get(i), sorts.get(i)), sorts.get(i)));
                }

                // [[des \in sub]]
                Expr inSub = ExprElementOf.make(new TermTuple(des), sub);
                Term term = recursivelyTranslate(inSub, context);
                terms.add(term);
                coeffs.add(1);

                done = true;
                for (int i = scopes.size() - 1; i >= 0; i--) {
                    if (deNums.get(i) < scopes.get(i)) {
                        deNums.set(i, deNums.get(i) + 1);
                        done = false;
                        break;
                    } else {
                        deNums.set(i, 1);
                    }
                }
            } while (!done);

            return new PbExpr(terms, coeffs);
        }

        @Override
        public PbExpr visit(ExprCall x) throws Err {
            // TODO recurse through calls so that e.g. integer/plus works
            //   This probably requires keeping track of a proper TranslationContext...
            return null;
        }

        @Override
        public PbExpr visit(ExprLet x) throws Err {
            // TODO: expand lets?
            return null;
        }

        @Override
        public PbExpr visit(ExprVar x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(ExprElementOf x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(ExprList x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(ExprQt x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(Sig x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(Sig.Field x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(Func x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(Assert x) throws Err {
            return null;
        }

        @Override
        public PbExpr visit(Macro macro) throws Err {
            return null;
        }
    }

}
