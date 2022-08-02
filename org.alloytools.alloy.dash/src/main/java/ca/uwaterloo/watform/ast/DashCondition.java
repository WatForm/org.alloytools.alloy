package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashCondition {

    private Pos    pos;
    private String name;
    private Expr   expr;

    public DashCondition(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
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
