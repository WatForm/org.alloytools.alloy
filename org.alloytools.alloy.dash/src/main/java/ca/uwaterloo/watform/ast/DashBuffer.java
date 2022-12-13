package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashBuffer extends DashSuperAST {

    private String param;

    public DashBuffer(Pos pos, String name, String param) {
	    super(pos, name);
        this.param = param;
    }
    
    public String getParam() {
    	return param;
    }
}
