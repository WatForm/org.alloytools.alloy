package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashHelper.ItemType;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

public class DashState extends DashSuperState {
	private List<DashEnter>		enter;
	private List<DashExit>  	exit;
	private List<DashTrans> 	modifiedTransitions; // Transitions after they have been modified during the transformation to Core Dash
	private final Boolean       isDefault;  		//Specifies whether this state is a default state

    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * state. items are the list of items that are inside the parsed state.
     */
    public DashState(Pos pos, String label, List<Object> stateItems, Boolean isDefault) {
    	super(pos, label);
        this.initializeContainers();
        
        if (stateItems != null) {
            for (Object item : stateItems) {
                if (item instanceof DashState)
                    this.states.add((DashState) item);
                if (item instanceof DashConcState)
                    this.concStates.add((DashConcState) item);
                if (item instanceof DashTrans)
                    this.transitions.add((DashTrans) item);
                if (item instanceof DashEnter) 
                    this.enter.add((DashEnter) item);
                if (item instanceof Decl)
                    decls.add((Decl) item);
                if (item instanceof DashEvent)
                    events.add((DashEvent) item);
                if (item instanceof DashEvent)
                    eventNames.add(((DashEvent) item).getRawName());
                if (item instanceof DashExit) 
                    this.exit.add((DashExit) item);
                if (item instanceof DashEvent)
                    this.events.add((DashEvent) item);
                if (item instanceof DashInvariant)
                    this.invariant.add((DashInvariant) item);
                if (item instanceof DashExpr)
                    throw new ErrorSyntax(((DashExpr) item).pos, "Illegal declaration inside a state");
            }
        }

        this.isDefault = isDefault;
    }
    
    private void initializeContainers() {
    	this.enter      			= new ArrayList<DashEnter>();
    	this.exit       			= new ArrayList<DashExit>();
    	this.modifiedTransitions    = new ArrayList<DashTrans>();
    }

	@Override
	public List<DashConcState> getInnerConcStates() {
		return this.concStates;
	}

	@Override
	public List<DashState> getInnerORStates() {
		return this.states;
	}
	
	@Override
	public List<DashSuperState> getInnerStatesDeepCopy() {
		List<DashSuperState> states = new ArrayList<DashSuperState>(this.concStates);
		states.addAll(new ArrayList<DashSuperState>(this.states));
		return states;
	}

	@Override
	public List<DashTrans> getTransitions() {
		return this.transitions;
	}
	
	@Override
	public List<DashBuffer> getBuffers(){
		return this.buffers;
	}

	@Override
	public List<String> getVariableNames(){
		return this.variables;
	}
	
	@Override
	public List<DashEvent> getEvents(){
		return this.events;
	}
	
	@Override
	public List<String> getEventNames(){
		return this.eventNames;
	}
	
	@Override
	public List<DashInvariant> getInvariants () {
		return this.invariant;
	}
	
	@Override
	public List<Decl> getVariables(){
		return this.decls;
	}
	
	@Override
	public List<DashAction> getActions() {
		return this.action;
	}
	
	@Override
	public List<DashCondition> getConditions() {
		return this.condition;
	}
	
    public List<DashEnter> getEnters() {
    	return this.enter;
    }
    
    public List<DashExit> getExits() {
    	return this.exit;
    }
    
    public List<DashTrans> getModifiedTransitions() {
    	return this.modifiedTransitions;
    }
    
    public void addModifiedTransition(DashTrans trans) {
    	this.modifiedTransitions.add(trans);
    }
    
    public boolean isDefault() {
    	return this.isDefault;
    }

	@Override
	public ItemType getType() {
		return ItemType.ORSTATE;
	}

	@Override
	public DashConcState getANDState() {
		return this.getParentConcState();
	}

}
