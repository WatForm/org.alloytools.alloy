package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public abstract class DashSuperState extends DashSuperAST {
    protected List<DashConcState>      concStates   = new ArrayList<DashConcState>();
    protected List<DashState>          states       = new ArrayList<DashState>();
    protected List<DashTrans> 		   transitions  = new ArrayList<DashTrans>();    
    
    public abstract List<DashConcState> getInnerConcStates();
    
    public abstract List<DashState> getInnerORStates();
    
    public abstract List<DashTrans> getTransitions();
}
