package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashInvariant extends DashSuperAST {
    private Expr          expr;
    // exprList is expr broken down into multiple expressions, that is: (expr = (expr0 AND expr1 AND expr2 ..) -> List[expr0, expr1, expr2))
    private List<Expr>    exprList = new ArrayList<Expr>();

    public DashInvariant(Pos pos, String name, Expr expr) {
        super(pos, name);
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
