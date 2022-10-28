package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;

/* This class is responsible for holding information regarding each concurrent state
 * declared within a DASH model */
public class DashConcState extends DashSuperState {
    private DashState			    				parentState;
    private String                  				param          = new String();
    
    private List<String>     	    				IEs   		   = new ArrayList<String>();
    private List<DashBuffer>        				buffers        = new ArrayList<DashBuffer>();
    private List<DashTemplateCall>  				templateCall   = new ArrayList<DashTemplateCall>();
    private List<DashTransTemplate> 				templateDecl   = new ArrayList<DashTransTemplate>();
    private List<DashEvent>         				events         = new ArrayList<DashEvent>();
    private List<Decl>              				decls          = new ArrayList<Decl>();
    private List<DashInit>          				init           = new ArrayList<DashInit>();
    private List<DashInvariant>     				invariant      = new ArrayList<DashInvariant>();
    private List<DashAction>        				action         = new ArrayList<DashAction>();
    private List<DashCondition>     				condition      = new ArrayList<DashCondition>();
    private List<DashTrans>     					allTransitions = new ArrayList<DashTrans>();
    private Map<Integer, List<DashConcState>>     	allChildConcStates = new LinkedHashMap<Integer, List<DashConcState>>();


    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * concurrent state. concStateItems are the list of items that are inside the
     * parsed conc state.
     */
    public DashConcState(Pos pos, String name, List<Object> concStateItems, ExprVar param) {
        this.pos = pos;
        this.name = name;

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

	public DashConcState(DashConcState concState) {
		this.name = concState.name;
		this.modifiedName = concState.modifiedName;
		this.parentConcState = concState.parentConcState;	
		this.concStates = concState.concStates;		
		this.states = concState.states;
		this.param = concState.param;
		this.transitions = concState.transitions;
		this.allTransitions = concState.allTransitions;
		this.templateCall = concState.templateCall;		
		this.templateDecl = concState.templateDecl;
		this.events = concState.events;
		this.decls = concState.decls;
		this.init = concState.init;		
		this.invariant = concState.invariant;
		this.action = concState.action;
		this.condition = concState.condition;
		this.buffers = concState.buffers;
		this.IEs = concState.IEs;
	}
	
	public DashState getParentORState() {
		return parentState;
	}
	
	public void setParentORState(DashState parentState) {
		this.parentState = parentState;
	}
	
	public void addAllTransition(DashTrans transition) {
		this.allTransitions.add(transition);
	}
	
	public Map<Integer, List<DashConcState>> getAllChildConcStates() {
		return allChildConcStates;
	}
	
	public boolean isParameterized () {
		return !param.isEmpty();
	}
	
	public String getReplicatedIdentifier() {
		return param;
	}
	
	public List<String> getIdentifiers() {
		return IEs;
	}
	
	public List<DashTemplateCall> getTemplateCalls(){
		return templateCall;
	}
	
	public List<DashTransTemplate> getTemplateDeclarations(){
		return templateDecl;
	}
	
	public List<DashTrans> getAllTransitions (){
		return allTransitions;
	}
	
	public List<DashBuffer> getBuffers(){
		return buffers;
	}
	
	public List<DashEvent> getEvents(){
		return events;
	}
	
	public List<Decl> getVariables(){
		return decls;
	}
	
	public List<DashInit> getInitialConds(){
		return init;
	}
	
	public List<DashInvariant> getInvariants () {
		return invariant;
	}
	public List<DashAction> getActions() {
		return action;
	}
	
	public List<DashCondition> getConditions() {
		return condition;
	}
	
	public void addInnerConcState(DashConcState concState) {
		int identifiers = concState.getIdentifiers().size();
		if(!(this.allChildConcStates).containsKey(identifiers)) {
			this.allChildConcStates.put(identifiers, new ArrayList<DashConcState>());
			this.allChildConcStates.get(identifiers).add(concState);
		}
		else {
			this.allChildConcStates.get(identifiers).add(concState);
		}
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
		DashConcState parent = new DashConcState(getParentConcState());
		while (parent != null) {
			parents.add(new DashConcState(parent));
			parent = parent.getParentConcState();
		}
		for (int i = parents.size() - 1; i >= 0; i--){
			if (parents.get(i).isParameterized())
				return parents.get(i);
		}
		return this;
	}
}
