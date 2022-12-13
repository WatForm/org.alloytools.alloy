package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashDoExpr extends DashSuperAST {
    private Expr       expr;
    // exprList is expr broken down into multiple expressions, that is: (expr = (expr0 AND expr1 AND expr2 ..) -> List[expr0, expr1, expr2))
    private List<Expr> exprList = new ArrayList<Expr>();

    public DashDoExpr(Pos pos, Expr expr) {
    	super(pos, null);
	    this.expr = expr;
    }
    
    public Expr getExpr() {
    	return expr;
    }
    
    public List<Expr> getAllExpression() {
    	return exprList;
    }
}
