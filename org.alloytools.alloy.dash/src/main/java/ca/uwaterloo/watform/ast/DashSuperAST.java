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
    
    public final Pos getPos() {
    	return this.pos;
    }
    
    public final String getRawName() {
    	return this.name;
    }
    
    public final String getFullyQualName() {
    	return this.modifiedName;
    }
    
    public final DashConcState getParentConcState () {
    	return this.parentConcState;
    }
    
    public final void setFullyQualName(String modifiedName) {
    	this.modifiedName = modifiedName;
    }
    
    public final void setRawName(String name) {
    	this.name = name;
    }
    
    public final void setParentConcState(DashConcState parentConcState) {
    	this.parentConcState = parentConcState;
    }
    
    public final DashSuperState getParent() {
    	return this.parent;
    }
    
    public final void setParent(DashSuperState actualParent) {
    	this.parent = actualParent;
    }
}
