package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashSend extends DashSuperAST {
    private Expr 	     param;

    public DashSend(Pos pos, String name) {
    	super(pos, name);
    }
    
    public DashSend(Pos pos, String name, Expr param) {
    	super(pos, name);
        this.param = param;
    }
    
    public DashSend (DashSend send) {
    	super(send.pos == null ? null : send.pos, send.name);
    	this.parentConcState = send.parentConcState == null ? null : send.parentConcState;
    	this.param = (send.param == null) ? null : send.param;
    }
    
    public Expr getEventsTriggered() {
    	return param;
    }
}
