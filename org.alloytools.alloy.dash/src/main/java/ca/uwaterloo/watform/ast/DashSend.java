package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashSend extends DashSuperAST {

    public Pos           pos;
    public Expr 	     param;

    public DashSend(Pos pos, String name) {
        this.pos = pos;
        this.name = name;
    }
    
    public DashSend(Pos pos, String name, Expr param) {
        this.pos = pos;
        this.name = name;
        this.param = param;
    }
    
    public DashSend (DashSend send) {
    	this.pos = send.pos == null ? null : send.pos;
    	this.parentConcState = send.parentConcState == null ? null : send.parentConcState;
    	this.param = (send.param == null) ? null : send.param;
    	this.name = send.name;
    }
    
    public Expr getEventsTriggered() {
    	return param;
    }
}
