package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public abstract class DashSuperAST {
	protected Pos                  pos;
	protected String               name         = "";
    protected String               modifiedName = "";
    
    protected Object          	   parent;
    protected DashConcState		   parentConcState;
    
    public Pos getPos() {
    	return pos;
    }
    
    public String getRawName() {
    	return name;
    }
    
    public String getFullyQualName() {
    	return modifiedName;
    }
    
    public DashConcState getParentConcState () {
    	return parentConcState;
    }
    
    public void setFullyQualName(String modifiedName) {
    	this.modifiedName = modifiedName;
    }
    
    public void setRawName(String name) {
    	this.name = name;
    }
    
    public void setParentConcState(DashConcState parentConcState) {
    	this.parentConcState = new DashConcState(parentConcState);
    }
    
    public Object getParent() {
    	return parent;
    }
    
    public void setParent(Object actualParent) {
    	this.parent = actualParent;
    }
}
