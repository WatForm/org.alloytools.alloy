package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashGoto extends DashSuperAST{
    private List<String> 			    gotoExpr = new ArrayList<String>();
    private Map<String, DashConcState>  gotoExprs = new LinkedHashMap<String, DashConcState>();
    private boolean 					enteringDefaultStates = false;
    private Expr       			 		param;
    
    public DashGoto(Pos pos, List<ExprVar> gotoExpr) {
        super(pos, null);
        
        if (gotoExpr.size() > 0) {
            for (ExprVar var : gotoExpr) {
                this.gotoExpr.add(var.toString());
            }
        }
    }
    
    public DashGoto(DashGoto gotoCom) {
    	super(gotoCom.pos, null);
    	this.gotoExpr = gotoCom.gotoExpr;
    	this.setDefaultStatesEntered(new LinkedHashMap<String, DashConcState>(gotoCom.getDefaultStatesEntered()));
    	this.setEnteringDefaultStates(gotoCom.isEnteringDefaultStates());
    	this.setRawName(gotoCom.name);
    	this.setDestination(gotoCom.getDestination());
    	this.setParentConcState(gotoCom.parentConcState);
    }

    /*
     * Used when the TransfromCoreDash expands transitions and creates a new
     * DashGoto Object
     */
    public DashGoto(Pos pos, List<String> gotoExpr, Expr param) {
    	super(pos, null);
        this.gotoExpr = new ArrayList<String>(gotoExpr);
        this.setDestination(param);
    }
    
    /*
     * Used by the Grammer file to create a parameterized Goto expression
     */
   public DashGoto(Pos pos, String gotoExpr, Expr param) {
	   super(pos, null);
       this.gotoExpr = new ArrayList<String>(Arrays.asList(gotoExpr));
       this.setDestination(param);
   }
    
    public DashGoto(List<String> gotoExpr) {
    	super(null, null);
        this.gotoExpr = new ArrayList<String>(gotoExpr);
    }

    public DashGoto(String gotoExpr) {
    	super(null, null);
        this.gotoExpr.add(gotoExpr);
    }
    
    public String getAlloyName() {
    	return gotoExpr.get(0).replace('/', '_');
    }
    
    public List<String> getAllDestinations() {
    	return gotoExpr;
    }
    
    public boolean isEnteringDefaultState() {
    	return isEnteringDefaultStates();
    }

	public Map<String, DashConcState> getDefaultStatesEntered() {
		return gotoExprs;
	}

	public void setDefaultStatesEntered (Map<String, DashConcState> gotoExprs) {
		this.gotoExprs = gotoExprs;
	}

	public boolean isEnteringDefaultStates() {
		return enteringDefaultStates;
	}

	public void setEnteringDefaultStates(boolean enteringDefaultStates) {
		this.enteringDefaultStates = enteringDefaultStates;
	}

	public Expr getDestination() {
		return param;
	}

	public void setDestination(Expr param) {
		this.param = param;
	}
}
