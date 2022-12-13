package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashExit extends DashSuperAST {
    private Expr expr;

    public DashExit(Pos pos, Expr expr) {
    	super(pos, null);
        this.setExpr(expr);
    }

	public Expr getExpr() {
		return expr;
	}

	public void setExpr(Expr expr) {
		this.expr = expr;
	}

}
