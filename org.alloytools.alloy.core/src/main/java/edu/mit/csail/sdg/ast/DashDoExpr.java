package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashDoExpr {

    public Pos        pos;
    public Expr       expr;
    public List<Expr> exprList = new ArrayList<Expr>();

    public DashDoExpr(Pos pos, Expr expr) {
        this.pos = pos;
        this.expr = expr;
    }
}
