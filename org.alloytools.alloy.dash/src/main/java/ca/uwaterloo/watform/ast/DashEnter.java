package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashEnter extends DashSuperAST {
    private Expr expr;

    public DashEnter(Pos pos, Expr expr) {
    	super(pos, null);
        this.expr = expr;
    }

    public Expr getExpr() {
    	return expr;
    }
}
