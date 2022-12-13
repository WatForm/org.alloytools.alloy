package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

public class DashEvent extends DashSuperAST {
    private String parentName = "";
    private String type       = "";
    private Decl   decl;
    private boolean isParameterized = false;

    public DashEvent(Pos pos, String name, String type) {
        super(pos, name);
        this.setType(type);
    }
    
    public DashEvent(Pos pos, Decl decl, String type) {
    	super(pos, null);
        this.setDecl(decl);
        this.setType(type);
    }
    
    public DashEvent(Pos pos, Decl decl, String type, boolean isParameterized) {
    	super(pos, null);
        this.setDecl(decl);
        this.setType(type);
        this.isParameterized = isParameterized;
    }
    
    public DashEvent(DashEvent event) {
    	super(null, event.name);
        this.parentName = event.parentName;
        this.modifiedName = event.modifiedName;
        this.setType(event.getType());
        this.setDecl(event.getDecl());
        this.parentConcState = event.parentConcState;
        this.isParameterized = event.isParameterized();
    }
    
    public String getParentName() {
    	return parentName;
    }
    
    public void setParentName(String parentName) {
    	this.parentName = parentName;
    }

	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public Decl getDecl() {
		return decl;
	}

	public void setDecl(Decl decl) {
		this.decl = decl;
	}

	public boolean isParameterized() {
		return isParameterized;
	}
}
