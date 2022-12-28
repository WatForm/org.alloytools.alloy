package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashHelper.ItemType;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

/*
 * The Base Class for DashState and DashConcState sub-class
 */
public abstract class DashSuperState extends DashSuperAST {
	protected List<DashConcState>      	concStates;
    protected List<DashState>          	states;
    protected List<DashTrans> 		  	transitions;
    protected List<Decl>          		decls;
    protected List<String>          	variables;
    protected List<DashEvent>    		events;
    protected List<DashAction>        	action;
    protected List<DashCondition>     	condition;
    protected List<DashBuffer>    		buffers;
    protected List<DashInvariant>     	invariant;  
    protected List<String>				eventNames;
    
    protected DashSuperState(Pos pos, String name) {
		super(pos, name);
		this.initializeContainers();
	}
    
    private void initializeContainers() {
    	concStates     = new ArrayList<>();
        states         = new ArrayList<>();
        transitions    = new ArrayList<>();
        decls          = new ArrayList<>();
        variables 	   = new ArrayList<>();
        events         = new ArrayList<>();
        action         = new ArrayList<>();
        condition      = new ArrayList<>();
        buffers        = new ArrayList<>();
        invariant      = new ArrayList<>();
        eventNames	   = new ArrayList<>();
    }
    
    public abstract List<DashConcState>	getInnerConcStates();
    public abstract List<DashState>	  	getInnerORStates();
    public abstract List<DashSuperState>getInnerStatesDeepCopy();
    public abstract List<DashTrans> 	getTransitions();
    public abstract List<DashBuffer>	getBuffers();
    public abstract List<DashEvent>	 	getEvents();
    public abstract List<String>	 	getEventNames();
    public abstract List<Decl> 		  	getVariables();
    public abstract List<String> 		getVariableNames();
	public abstract List<DashAction> 	getActions();
	public abstract List<DashCondition> getConditions();
	public abstract List<DashInvariant> getInvariants ();
    
    public abstract ItemType getType();
    // Return the object if it of type DashConc,
    // If it is of type DashState, then return the parent AND state
    public abstract DashConcState getANDState();
} 
