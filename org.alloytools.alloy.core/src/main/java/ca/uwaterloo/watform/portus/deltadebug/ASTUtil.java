package ca.uwaterloo.watform.portus.deltadebug;

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
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Utilities for manipulating the Alloy AST.
 */
final class ASTUtil {

    /**
     * Get the list of children of expr.
     */
    public static List<Expr> getChildren(Expr expr) {
        return new VisitReturn<List<Expr>>() {
            @Override
            public List<Expr> visit(ExprBinary x) throws Err {
                return Arrays.asList(x.left, x.right);
            }

            @Override
            public List<Expr> visit(ExprList x) throws Err {
                return x.args;
            }

            @Override
            public List<Expr> visit(ExprCall x) throws Err {
                return x.args;
            }

            @Override
            public List<Expr> visit(ExprConstant x) throws Err {
                return Collections.emptyList(); // leaf
            }

            @Override
            public List<Expr> visit(ExprITE x) throws Err {
                return Arrays.asList(x.cond, x.left, x.right);
            }

            @Override
            public List<Expr> visit(ExprLet x) throws Err {
                return Arrays.asList(x.expr, x.sub);
            }

            @Override
            public List<Expr> visit(ExprQt x) throws Err {
                List<Expr> children = x.decls.stream().map(decl -> decl.expr).collect(Collectors.toList());
                children.add(x.sub);
                return children;
            }

            @Override
            public List<Expr> visit(ExprUnary x) throws Err {
                return Collections.singletonList(x.sub);
            }

            @Override
            public List<Expr> visit(ExprVar x) throws Err {
                return Collections.emptyList(); // leaf
            }

            @Override
            public List<Expr> visit(Sig x) throws Err {
                return Collections.emptyList(); // leaf
            }

            @Override
            public List<Expr> visit(Sig.Field x) throws Err {
                return Collections.emptyList(); // leaf
            }

            @Override
            public List<Expr> visit(Func x) throws Err {
                throw new ErrorFatal("Cannot get children of Func!");
            }

            @Override
            public List<Expr> visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot get children of Func!");
            }

            @Override
            public List<Expr> visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot get children of Func!");
            }
        }.visitThis(expr);
    }

    /**
     * Replace the child `from` with `to` in the children of `parent`.
     */
    public static Expr replaceChild(Expr parent, Expr from, Expr to) {
        // sigh - have to do this per expr type
        return new VisitReturn<Expr>() {
            private Expr tryReplace(Expr expr) {
                if (expr.isSame(from)) {
                    return to;
                } else {
                    return expr;
                }
            }

            private List<Expr> tryReplaceList(List<Expr> exprs) {
                return exprs.stream()
                        .map(this::tryReplace)
                        .collect(Collectors.toList());
            }

            @Override
            public Expr visit(ExprBinary x) throws Err {
                return x.op.make(x.pos, x.closingBracket, tryReplace(x.left), tryReplace(x.right));
            }

            @Override
            public Expr visit(ExprList x) throws Err {
                return ExprList.make(x.pos, x.closingBracket, x.op, tryReplaceList(x.args));
            }

            @Override
            public Expr visit(ExprCall x) throws Err {
                // TODO: not looking in function body, ok??
                return ExprCall.make(x.pos, x.closingBracket, x.fun, tryReplaceList(x.args), x.extraWeight);
            }

            @Override
            public Expr visit(ExprConstant x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprITE x) throws Err {
                return ExprITE.make(x.pos, tryReplace(x.cond), tryReplace(x.left), tryReplace(x.right));
            }

            @Override
            public Expr visit(ExprLet x) throws Err {
                // not replacing var, should be okay
                return ExprLet.make(x.pos, x.var, tryReplace(x.expr), tryReplace(x.sub));
            }

            @Override
            public Expr visit(ExprQt x) throws Err {
                // TODO: not replacing decls, ok??
                return x.op.make(x.pos, x.closingBracket, x.decls, tryReplace(x.sub));
            }

            @Override
            public Expr visit(ExprUnary x) throws Err {
                return x.op.make(x.pos, tryReplace(x.sub));
            }

            @Override
            public Expr visit(ExprVar x) throws Err {
                return x;
            }

            @Override
            public Expr visit(Sig x) throws Err {
                return x;
            }

            @Override
            public Expr visit(Sig.Field x) throws Err {
                return x;
            }

            @Override
            public Expr visit(Func x) throws Err {
                throw new ErrorFatal("Cannot visit Func!");
            }

            @Override
            public Expr visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot visit Assert!");
            }

            @Override
            public Expr visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot visit Macro!");
            }
        }.visitThis(parent);
    }

    /**
     * Replace the children of expr with the given children.
     */
    public static Expr replaceChildren(Expr expr, List<Expr> children) {
        return new VisitReturn<Expr>() {
            private void checkSize(int size) {
                if (children.size() != size) {
                    throw new ErrorFatal("Cannot replace children of " + expr + " with " + children
                            + ", expected size=" + size);
                }
            }

            private Expr child(int idx) { // convenience
                return children.get(idx);
            }

            @Override
            public Expr visit(ExprBinary x) throws Err {
                checkSize(2);
                return x.op.make(x.pos, x.closingBracket, child(0), child(1));
            }

            @Override
            public Expr visit(ExprList x) throws Err {
                return ExprList.make(x.pos, x.closingBracket, x.op, children);
            }

            @Override
            public Expr visit(ExprCall x) throws Err {
                return ExprCall.make(x.pos, x.closingBracket, x.fun, children, x.extraWeight);
            }

            @Override
            public Expr visit(ExprConstant x) throws Err {
                checkSize(0);
                return x; // leaf
            }

            @Override
            public Expr visit(ExprITE x) throws Err {
                checkSize(3);
                return ExprITE.make(x.pos, child(0), child(1), child(2));
            }

            @Override
            public Expr visit(ExprLet x) throws Err {
                checkSize(2); // [expr, sub]
                return ExprLet.make(x.pos, x.var, child(0), child(1));
            }

            @Override
            public Expr visit(ExprQt x) throws Err {
                checkSize(x.decls.size() + 1); // all the decls' exprs, then sub

                // Manually replace the exprs in the decls
                List<Decl> newDecls = new ArrayList<>();
                for (int idx = 0; idx < x.decls.size(); idx++) {
                    Decl decl = x.decls.get(idx);
                    Expr newExpr = child(idx);
                    newDecls.add(new Decl(
                            decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar,
                            decl.names, newExpr));
                }
                Expr newSub = child(x.decls.size());

                return x.op.make(x.pos, x.closingBracket, newDecls, newSub);
            }

            @Override
            public Expr visit(ExprUnary x) throws Err {
                checkSize(1);
                return x.op.make(x.pos, child(0));
            }

            @Override
            public Expr visit(ExprVar x) throws Err {
                checkSize(0);
                return x; // leaf
            }

            @Override
            public Expr visit(Sig x) throws Err {
                checkSize(0);
                return x; // leaf
            }

            @Override
            public Expr visit(Sig.Field x) throws Err {
                checkSize(0);
                return x; // leaf
            }

            @Override
            public Expr visit(Func x) throws Err {
                throw new ErrorFatal("Cannot visit Func!");
            }

            @Override
            public Expr visit(Assert x) throws Err {
                throw new ErrorFatal("Cannot visit Assert!");
            }

            @Override
            public Expr visit(Macro macro) throws Err {
                throw new ErrorFatal("Cannot visit Macro!");
            }
        }.visitThis(expr);
    }

}
