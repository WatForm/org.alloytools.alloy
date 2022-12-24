package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashHelper.ItemType;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;

/* This class is responsible for holding information regarding each concurrent state
 * declared within a DASH model */
public class DashConcState extends DashSuperState {
    private DashState			    				parentState;
    private String                  				param;
    private List<String>     	    				IEs;
    private List<DashTemplateCall>  				templateCall;
    private List<DashTransTemplate> 				templateDecl;
    private List<DashInit>          				init;
    private List<DashTrans>     					allTransitions;
    private Map<Integer, List<DashConcState>>    	allChildConcStates;


    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * concurrent state. concStateItems are the list of items that are inside the
     * parsed conc state.
     */
    public DashConcState(Pos pos, String name, List<Object> concStateItems, ExprVar param) {
        super(pos, name);
        initializeContainers();
        //Iterate through each item in the conc state and add each item to
        //a respective list (A state item will be added to the list of states, etc)
        for (Object item : concStateItems) {
            if (item instanceof DashConcState) 
                concStates.add((DashConcState) item);
            if (item instanceof DashState)
                states.add((DashState) item);
            if (item instanceof DashTrans) 
                transitions.add((DashTrans) item);
            if (item instanceof Decl)
                decls.add((Decl) item);
            if (item instanceof DashEvent)
                events.add((DashEvent) item);
            if (item instanceof DashEvent)
                eventNames.add(((DashEvent) item).getRawName());
            if (item instanceof DashInit)
                init.add((DashInit) item);
            if (item instanceof DashInvariant)
                invariant.add((DashInvariant) item);
            if (item instanceof DashAction)
                action.add((DashAction) item);
            if (item instanceof DashCondition)
                condition.add((DashCondition) item);
            if (item instanceof DashTemplateCall)
                templateCall.add((DashTemplateCall) item);
            if (item instanceof DashTransTemplate)
                templateDecl.add((DashTransTemplate) item);
            if (item instanceof DashBuffer) 
                buffers.add((DashBuffer) item);
        }
        
        if (param != null)
        {
        	this.param = param.toString();
        }
        
        this.IEs = new ArrayList<String>();
    }
    
    private void initializeContainers() {
        param          = new String();
        IEs   		   = new ArrayList<String>();
        templateCall   = new ArrayList<DashTemplateCall>();
        templateDecl   = new ArrayList<DashTransTemplate>();
        init           = new ArrayList<DashInit>();
        allTransitions = new ArrayList<DashTrans>();
        allChildConcStates = new LinkedHashMap<Integer, List<DashConcState>>();
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
	public List<DashTrans> getTransitions() {
		return this.transitions;
	}
	
	@Override
	public List<DashBuffer> getBuffers(){
		return this.buffers;
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
	public List<DashAction> getActions() {
		return this.action;
	}
	
	@Override
	public List<DashCondition> getConditions() {
		return this.condition;
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
	public ItemType getType() {
		return ItemType.ANDSTATE;
	}
	
	@Override 
	public DashConcState getANDState() {
		return (DashConcState) this;
	}
	
	public DashState getParentORState() {
		return this.parentState;
	}
	
	public void setParentORState(DashState parentState) {
		this.parentState = parentState;
	}
	
	public void addAllTransition(DashTrans transition) {
		this.allTransitions.add(transition);
	}
	
	public Map<Integer, List<DashConcState>> getAllChildConcStates() {
		return this.allChildConcStates;
	}
	
	public boolean isParameterized () {
		return !this.param.isEmpty();
	}
	
	public String getReplicatedIdentifier() {
		return this.param;
	}
	
	public List<String> getIdentifiers() {
		return this.IEs;
	}
	
	public List<DashTemplateCall> getTemplateCalls(){
		return this.templateCall;
	}
	
	public List<DashTransTemplate> getTemplateDeclarations(){
		return this.templateDecl;
	}
	
	public List<DashTrans> getAllTransitions (){
		return this.allTransitions;
	}
	
	public List<DashInit> getInitialConds(){
		return this.init;
	}
	
	public void addInnerConcState(DashConcState concState) {
		int identifiers = concState.getIdentifiers().size();
		this.allChildConcStates.getOrDefault(identifiers, new ArrayList<DashConcState>()).add(concState);
	}
	
	public void addSelfToInnerConcState() {
		int identifiers = getIdentifiers().size();
		if(!this.allChildConcStates.containsKey(identifiers)) {
			this.allChildConcStates.put(identifiers, new ArrayList<DashConcState>());
			this.allChildConcStates.get(identifiers).add(this);
		}
		else {
			this.allChildConcStates.get(identifiers).add(this);
		}
	}
	
	public DashConcState getTopParentRepConcState() {
		List<DashConcState> parents = new ArrayList<DashConcState>();
		DashConcState parent = getParentConcState();
		while (parent != null) {
			parents.add(parent);
			parent = parent.getParentConcState();
		}
		for (int i = parents.size() - 1; i >= 0; i--){
			if (parents.get(i).isParameterized())
				return parents.get(i);
		}
		return this;
	}
}
