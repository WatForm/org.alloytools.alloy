package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashGoto {

    public Pos          			  pos;
    public List<String> 			  gotoExpr = new ArrayList<String>();
    public DashConcState 	  		  gotoConcState;
    public Map<String, DashConcState> gotoExprs = new LinkedHashMap<String, DashConcState>();
    public boolean 					  enteringDefaultStates = false;
    public String       			  name;
    public Expr       			  param;
    
    public DashGoto(Pos pos, List<ExprVar> gotoExpr) {
        this.pos = pos;

        if (gotoExpr.size() > 0) {
            for (ExprVar var : gotoExpr) {
                this.gotoExpr.add(var.toString());
            }
        }
    }
    
    public DashGoto(DashGoto gotoCom) {
    	this.pos = gotoCom.pos;
    	this.gotoExpr = gotoCom.gotoExpr;
    	this.gotoExprs = new LinkedHashMap<String, DashConcState>(gotoCom.gotoExprs);
    	this.enteringDefaultStates = gotoCom.enteringDefaultStates;
    	this.name = gotoCom.name;
    	this.param = gotoCom.param;
    	this.gotoConcState = gotoCom.gotoConcState;
    }

    /*
     * Used when the TransfromCoreDash expands transitions and creates a new
     * DashGoto Object
     */
    public DashGoto(Pos pos, List<String> gotoExpr, Expr param) {
        this.pos = pos;
        this.gotoExpr = new ArrayList<String>(gotoExpr);
        this.param = param;
    }
    
    /*
     * Used by the Grammer file to create a parameterized Goto expression
     */
   public DashGoto(Pos pos, String gotoExpr, Expr param) {
       this.pos = pos;
       this.gotoExpr = new ArrayList<String>(Arrays.asList(gotoExpr));
       this.param = param;
   }
    
    public DashGoto(List<String> gotoExpr) {
        this.pos = null;
        this.gotoExpr = new ArrayList<String>(gotoExpr);
    }

    public DashGoto(String gotoExpr) {
        this.pos = null;
        this.gotoExpr.add(gotoExpr);
    }
    
    public String getAlloyName() {
    	return gotoExpr.get(0).replace('/', '_');
    }
    
    public List<String> getAllDestinations() {
    	return gotoExpr;
    }
    
    public boolean isEnteringDefaultState() {
    	return enteringDefaultStates;
    }
}
