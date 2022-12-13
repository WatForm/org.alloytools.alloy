package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashWhenExpr extends DashSuperAST {
    private Expr       expr;
    private List<Expr> exprList = new ArrayList<Expr>();

    public DashWhenExpr(Pos pos, Expr expr) {
        super(pos, null);
        this.setExpr(expr);
    }

	public Expr getExpr() {
		return expr;
	}

	public void setExpr(Expr expr) {
		this.expr = expr;
	}

	public List<Expr> getAllExpressions() {
		return exprList;
	}

	public void setAllExpressions(List<Expr> exprList) {
		this.exprList = exprList;
	}
}
