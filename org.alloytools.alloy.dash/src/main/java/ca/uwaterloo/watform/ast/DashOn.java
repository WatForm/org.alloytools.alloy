package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashOn extends DashSuperAST {
    private Boolean 		 isInternal = false;

    public DashOn(Pos pos, String name, Boolean isInternal) {
        super(pos, name);
        this.setIsInternal(isInternal);
    }
    
    public DashOn(DashOn on) {
    	super(on.pos, on.name);
    	this.parentConcState = on.parentConcState;
    	this.setIsInternal(on.isInternal());
    }

	public Boolean isInternal() {
		return isInternal;
	}

	public void setIsInternal(Boolean isInternal) {
		this.isInternal = isInternal;
	}
}
