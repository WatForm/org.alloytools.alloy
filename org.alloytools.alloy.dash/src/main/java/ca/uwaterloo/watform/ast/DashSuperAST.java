package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

/*
 * All Dash AST classes will inherit this class as their base class
 */
public abstract class DashSuperAST {
	protected Pos                  pos;
	protected String               name;
    protected String               modifiedName; 
    protected DashSuperState       parent;
    protected DashConcState		   parentConcState;
    
    public DashSuperAST(Pos pos, String name) {
    	this.pos = pos;
    	this.name = name;
    }
    
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
    	this.parentConcState = parentConcState;
    }
    
    public Object getParent() {
    	return parent;
    }
    
    public void setParent(DashSuperState actualParent) {
    	this.parent = actualParent;
    }
}
