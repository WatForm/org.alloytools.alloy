package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashOn extends DashSuperAST {

    public Pos    	     pos;
    public Boolean 		 isInternal = false;

    public DashOn(Pos pos, String name, Boolean isInternal) {
        this.pos = pos;
        this.name = name;
        this.isInternal = isInternal;
    }
    
    public DashOn(DashOn on) {
    	this.pos = on.pos;
    	this.parentConcState = on.parentConcState;
    	this.name = on.name;
    	this.isInternal = on.isInternal;
    }
}
