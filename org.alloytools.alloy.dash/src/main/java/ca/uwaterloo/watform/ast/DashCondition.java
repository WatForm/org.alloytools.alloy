package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashCondition extends DashSuperAST {
    private Expr   expr;

    public DashCondition(Pos pos, String name, Expr expr) {
        super(pos, name);
        this.expr = expr;
    }
    
    public Pos getPos () {
    	return pos;
    }
    
    public String getRawName() {
    	return name;
    }
    
    public Expr getExpr() {
    	return expr;
    }
}
