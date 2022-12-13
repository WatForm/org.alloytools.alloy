package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

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
                if (item instanceof DashExit) 
                    this.exit.add((DashExit) item);
                if (item instanceof DashEvent)
                    throw new ErrorSyntax(((DashEvent) item).pos, "Cannot declare an event inside a state");
                if (item instanceof DashExpr)
                    throw new ErrorSyntax(((DashExpr) item).pos, "Illegal declaration inside a state");
            }
        }

        this.isDefault = isDefault;
    }
    
    private void initializeContainers() {
    	enter      			= new ArrayList<DashEnter>();
    	exit       			= new ArrayList<DashExit>();
    	modifiedTransitions = new ArrayList<DashTrans>();
    }

	@Override
	public List<DashConcState> getInnerConcStates() {
		return concStates;
	}

	@Override
	public List<DashState> getInnerORStates() {
		return states;
	}

	@Override
	public List<DashTrans> getTransitions() {
		return transitions;
	}
	
	@Override
	public List<DashBuffer> getBuffers(){
		return buffers;
	}
	
	@Override
	public List<DashEvent> getEvents(){
		return events;
	}
	
	@Override
	public List<Decl> getVariables(){
		return decls;
	}

    public List<DashEnter> getEnters() {
    	return enter;
    }
    
    public List<DashExit> getExits() {
    	return exit;
    }
    
    public List<DashTrans> getModifiedTransitions() {
    	return modifiedTransitions;
    }
    
    public void addModifiedTransition(DashTrans trans) {
    	modifiedTransitions.add(trans);
    }
    
    public boolean isDefault() {
    	return isDefault;
    }

}
