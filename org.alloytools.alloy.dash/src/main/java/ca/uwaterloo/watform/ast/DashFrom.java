package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashFrom extends DashSuperAST {
    private List<String> 			 	fromExpr = new ArrayList<String>();
    private List<DashConcState> 		fromExprs = new ArrayList<DashConcState>();
    private Boolean      				leavingMultipleStates;
    private String      				stateBeingLeft;
    private DashConcState				concStateBeingExited;
    private Boolean      				fromAll;

    public DashFrom(Pos pos, List<ExprVar> fromExpr, Boolean fromAll) {
        super(pos, null);

        if (fromExpr.size() > 0) {
            for (ExprVar var : fromExpr) {
                this.getAllOrigins().add(var.toString());
            }
        }
        this.setLeavingAllStates(fromAll);
        this.setLeavingMultipleStates(false);
    }

    public DashFrom(List<String> fromExpr, Boolean fromAll) {
    	super(null, null);
        this.setAllOrigins(fromExpr);
        this.setLeavingAllStates(fromAll);
        this.setLeavingMultipleStates(false);
    }

    public DashFrom(String fromExpr, Boolean fromAll) {
    	super(null, null);
        this.getAllOrigins().add(fromExpr);
        this.setLeavingAllStates(fromAll);
        this.setLeavingMultipleStates(false);
    }
    
    public String getAlloyName() {
    	return getAllOrigins().get(0).replace('/', '_');
    }

    public boolean isTransitionToParentState() {
    	return leavingMultipleStates;
    }
    
	public void setLeavingMultipleStates(Boolean leavingMultipleStates) {
		this.leavingMultipleStates = leavingMultipleStates;
	}

	public List<String> getAllOrigins() {
		return fromExpr;
	}

	public void setAllOrigins(List<String> fromExpr) {
		this.fromExpr = fromExpr;
	}

	public List<DashConcState> getConcStatesExited() {
		return fromExprs;
	}

	public void setConcStatesExited(List<DashConcState> fromExprs) {
		this.fromExprs = fromExprs;
	}

	public String getStateBeingLeft() {
		return stateBeingLeft;
	}

	public void setStateBeingLeft(String stateBeingLeft) {
		this.stateBeingLeft = stateBeingLeft;
	}

	public DashConcState getConcStateExited() {
		return concStateBeingExited;
	}

	public void setConcStateExited(DashConcState concStateBeingExited) {
		this.concStateBeingExited = concStateBeingExited;
	}

	public Boolean isLeavingAllStates() {
		return fromAll;
	}

	public void setLeavingAllStates(Boolean fromAll) {
		this.fromAll = fromAll;
	}
}
