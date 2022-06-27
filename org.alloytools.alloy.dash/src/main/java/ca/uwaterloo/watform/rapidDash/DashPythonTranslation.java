package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashModule;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;

import java.util.*;
import java.util.stream.Collectors;

import static edu.mit.csail.sdg.alloy4.TableView.clean;
import edu.mit.csail.sdg.alloy4.ConstList;

/**
 * Mutable; this class represents an Dash to Python translation module
 */

public class DashPythonTranslation {

    private DashModule dashModule;

    public List<Signature> signatures;
    public List<Event> allEnvEvents = new ArrayList<Event>();
    public State rootState = null;
    private Map<String, State> concStateMap;

    public class Signature {
        public String name;
        public String multiplicity;
        public int cardinality;
        public boolean isSubset;
        public List<String> parents;
        public boolean isSubsig;
        public String parent;
        public boolean isAbstract;

        public Signature(String name, String multiplicity, int cardinality, boolean isSubset, List<String> parents
                , boolean isSubsig, String parent, boolean isAbstract) {
            this.name = name;
            this.multiplicity = multiplicity;
            this.cardinality = cardinality;
            this.isSubset = isSubset;
            this.parents = parents;
            this.isSubsig = isSubsig;
            this.parent = parent;
            this.isAbstract = isAbstract;
        }

        public String getName() { return name; }
        public String getMultiplicity() { return multiplicity; }
        public int getCardinality() { return cardinality; }
        public String getIsSubset() {
            if (this.isSubset)
                return "True";
            return "False";
        }
        public String getParents() {
            return "{" + String.join(",", this.parents) + "}";
        }
        public String getIsSubsig() {
            if (this.isSubsig)
                return "True";
            return "False";
        }
        public String getParent() {
            if (this.parent != null)
                return this.parent;
            return "None";
        }
        public String getIsAbstract() {
            if (this.isAbstract)
                return "True";
            return "False";
        }
    }
    
    public class Event {
    	private String name;
    	private String modifiedName;
    	private boolean isEnvEvent;
    	private State parent;
    	
    	public Event(String name, String modifiedName, String type, State parent) {
    		this.name = name;
    		this.modifiedName = modifiedName;
    		this.isEnvEvent = type.equals("env event");
    		this.parent = parent;
    	}
    	
    	public String getModifiedName() {
    		return modifiedName;
    	}
    }

    /**
     * Constructs a new DashPythonTranslation object
     * @param dashModule - the DashModule we want to translate
     */
    public DashPythonTranslation(DashModule dashModule) {
        this.dashModule = dashModule;

        // Sort the signatures based on dependencies
        // TODO may need topological sort later to improve performance
        // I am using a not efficient starightforward sorting algorithm for now
        ArrayList<Sig> signaturesOriginalList = new ArrayList<Sig>(dashModule.sigs.values());
        ArrayList<Sig> signaturesSortedList = new ArrayList<Sig>();
        ArrayList<String> covered = new ArrayList<String>();
        while (signaturesOriginalList.size() != 0) {
            for (Sig sig : signaturesOriginalList){
                if (sig.isSubsig != null) {
                    if (((Sig.PrimSig) sig).parent == Sig.UNIV || covered.contains(clean(((Sig.PrimSig) sig).parent.label))) {
                        signaturesSortedList.add(sig);
                        signaturesOriginalList.remove(sig);
                        covered.add(clean(sig.label));
                        break;
                    }
                }
                if (sig.isSubset != null) {
                    ArrayList<String> parentsList = new ArrayList<String>();
                    for (Sig p : ((Sig.SubsetSig) sig).parents)
                        parentsList.add(clean(p.label));
                    if (covered.containsAll(parentsList)) {
                        signaturesSortedList.add(sig);
                        signaturesOriginalList.remove(sig);
                        covered.add(clean(sig.label));
                        break;
                    }
                }
            }

        }

        // get signature names
        this.signatures = signaturesSortedList.stream()
                .map(sig -> {
                    List<String> parents = new ArrayList<String>();
                    if (sig.isSubset != null)
                        for (Sig p : ((Sig.SubsetSig) sig).parents)
                            parents.add(clean(p.label));
                    boolean isSubsig = sig.isSubsig != null && ((Sig.PrimSig) sig).parent != Sig.UNIV;
                    String parent = null;
                    if (isSubsig)
                        parent = clean(((Sig.PrimSig) sig).parent.label);
                    return new Signature(clean(sig.label), getMultiplicity(sig), getCardinality(sig),
                            sig.isSubset != null, parents, isSubsig, parent, sig.isAbstract != null);
                })
                .collect(Collectors.toList());

        // get state hierarchy
        this.concStateMap = new HashMap<>();
        // initialize all states instances
        for(String stateName: dashModule.getAllConcurrentStates().keySet()){
            this.concStateMap.put(stateName, new State(stateName, true));
        }
        for(String stateName: dashModule.getORStates().keySet()){
            this.concStateMap.put(stateName, new State(stateName, false));
        }

        for(DashConcState state: dashModule.getAllConcurrentStates().values()) {
            if(rootState == null) {
                rootState = this.concStateMap.get(state.getFullyQualName());
            }

        	// add state variable declarations (decls)
        	for(Decl decl: state.getVariables()) {
        		DashExprToPython dashExprTranslator = new DashExprToPython<>(decl.expr);
        		dashExprTranslator.isDecl = true;
        		this.concStateMap.get(state.getFullyQualName()).addDecl("self." + decl.get() + " = " + dashExprTranslator.toString());
        	}
        	// add state variable initializations and constraints (inits and init_constraints)
        	for(DashInit init: state.getInitialConds()) {
        		for(Expr expr: init.getAllExpressions()) {
        			// if the Dash init func is empty, there will be one expr that says "true"
        			if(expr.toString().equals("true")) {
        				continue;
        			}
        			DashExprToPython dashExprTranslator = new DashExprToPython<>(expr);
        			// TODO: this (and DashExprToPython) needs to be cleaned up
        			dashExprTranslator.isInit = true;
        			dashExprTranslator.reparseExpr();
        			
        			// if the expression is a constraint on a variable's cardinality, add "assert"
        			// TODO: are other initialization constraint types possible? They need to be handled here
        			if(expr instanceof ExprBinary) {
        				ExprBinary binaryNode = (ExprBinary) expr;
        				if(binaryNode.left instanceof ExprUnary && ((ExprUnary)binaryNode.left).op == ExprUnary.Op.CARDINALITY) {
        					this.concStateMap.get(state.getFullyQualName()).addInitConstraint("assert " + dashExprTranslator.toString());
        					continue;
        				}
        			}
            		this.concStateMap.get(state.getFullyQualName()).addInit(dashExprTranslator.toString());
        		}
        	}
        	
        	// add state events
        	for(DashEvent event: state.getEvents()) {
        		Event newEvent = new Event(event.getRawName(), event.getFullyQualName(), event.getType(), this.concStateMap.get(state.getFullyQualName()));
        		this.concStateMap.get(newEvent);
        		if(newEvent.isEnvEvent) {
        			allEnvEvents.add(newEvent);
        		}
        	}
        	     	
        	// add substates to conc states
        	for(DashState substate: state.getInnerORStates()) {
        		this.concStateMap.get(state.getFullyQualName()).addSubstate(this.concStateMap.get(substate.getFullyQualName()));
        		this.concStateMap.get(substate.getFullyQualName()).parent = concStateMap.get(state.getFullyQualName());
        	}
        }
        
        // add substates to dash states
        for(DashState state: dashModule.getORStates().values()) {
        	for(DashState substate: state.getInnerORStates()) {
        		this.concStateMap.get(state.getFullyQualName()).addSubstate(this.concStateMap.get(substate.getFullyQualName()));
        		this.concStateMap.get(substate.getFullyQualName()).parent = concStateMap.get(state.getFullyQualName());
        	}
        }

        // generate transitions
        for(DashTrans dashTrans : dashModule.getTransitions().values()){
            Transition trans = new Transition(dashTrans);
            this.concStateMap.get(trans.getStateName()).addTransition(trans);
        }
    }

    private String getMultiplicity(Sig sig) {
        if (sig.isLone != null)
            return "lone";
        if (sig.isOne != null)
            return "one";
        if (sig.isSome != null)
            return "some";
        return "set";
    }

    private int getCardinality(Sig sig) {
        if (sig.isAbstract != null)
            return 0;
        if (sig.isOne !=null || sig.isLone != null)
            return 1;
        return 3;
    }

    // return all states that aren't substates (to prevent them from appearing multiple times)
    public List<State> getStates() {
    	List<State> states = new ArrayList<State>();
    	for(State state: concStateMap.values()) {
    		if(state.parent == null) {
    			states.add(state);
    		}
    	}
    	return states;
    }

    private Boolean isOneSig(Sig sig) {
        return sig.isOne != null & sig.isAbstract == null & sig.isEnum == null &
                sig.isLone == null & sig.isMeta == null & sig.isPrivate == null & sig.isSome == null & sig.isSubset == null &
                sig.isVariable == null;
    }

    public class State{
        private String stateName;                       // state name
        private List<Transition>  transitions;   // store the translated code for transitions
        private List<State> substates;
        private List<String> decls;
        private List<String> inits;
        private List<String> init_constraints;

        private boolean isConc;
        private List<Event> events;
        public State parent = null;
        public State(String stateName, boolean isConc){
            this.stateName = stateName;
            this.transitions = new ArrayList<>();
            this.substates = new ArrayList<State>();
            this.decls = new ArrayList<String>();
            this.inits = new ArrayList<String>();
            this.init_constraints = new ArrayList<String>();
            this.isConc = isConc;
        }
        public void addTransition(Transition transition){
            this.transitions.add(transition);
        }
        public String getName(){return stateName;}
        public List<Transition> getTransitions() {return transitions.stream().collect(Collectors.toList());}
        public List<State> getSubstates() { return substates.stream().collect(Collectors.toList()); }
        public List<String> getDecls() { return decls.stream().collect(Collectors.toList()); }
        public List<String> getInits() { return inits.stream().collect(Collectors.toList()); }
        public List<String> getInitConstraints() { return init_constraints.stream().collect(Collectors.toList()); }
        public List<Event> getEvents() { return events.stream().collect(Collectors.toList()); }

        public boolean getIsConc() {return isConc;}

        public void addSubstate(State s) { substates.add(s); }
        public void addDecl(String s) { decls.add(s); }
        public void addInit(String s) { inits.add(s); }
        public void addInitConstraint(String s) { init_constraints.add(s); }
        public void addEvent(Event e) { events.add(e); }
    }

    public class Transition{
        private String stateName;                       // state name

        private String fromStateName = "";
        private String toStateName = "";
        private String transName = "";                       // transition name
        private String action = "";                          // the logic for this transition to be executed
        private String guardCondition = "";                  // the guard condition of this transition
        private String eventCondition = "";
        private String triggerEvent = "";
        private String transTemplate = "";

        public Transition(DashTrans dashTrans){
            // set default transition information
            this.transName = dashTrans.getRawName();
            if (dashTrans.getParent() instanceof DashConcState) {
                this.stateName = ((DashConcState)dashTrans.getParent()).getFullyQualName();
            } else {
                this.stateName = ((DashState)dashTrans.getParent()).getFullyQualName();
            }

            // check keywords
            if(dashTrans.getOrigin() != null){    // determines which state this transition belongs to
                this.fromStateName = dashTrans.getOrigin().getAllOrigins().get(0);
            }
            if(dashTrans.getTriggerEvent() != null){      // determines the trigger event
                this.eventCondition = dashTrans.getTriggerEvent().getRawName();
            }
            if(dashTrans.getCondition() != null){    // determines the guard_condition (if statement)
                DashExprToPython dashExprTranslator = new DashExprToPython<>(dashTrans.getCondition());

                // set condition
                this.guardCondition = dashExprTranslator.toString();
            }
            if(dashTrans.getAction() != null){      // determines the action
                DashExprToPython dashExprTranslator = new DashExprToPython<>(dashTrans.getAction());

                // set action
                this.action = dashExprTranslator.toString();
            }
            if(dashTrans.getDestination() != null){    // determine the next state
                this.toStateName = dashTrans.getDestination().toString();
            }
            if(dashTrans.getEventsTriggered() != null){    // determines the event to send
                this.triggerEvent = dashTrans.getEventsTriggered().getRawName();
            }
            if(dashTrans.getTransTemplate() != null){   // TODO: don't know what this does
                this.transTemplate = "pass\t# <placeholder for Trans Template>";
            }
        }
        public String getTransName(){return transName;}
        public String getStateName(){return stateName;}
        public String getGuardCondition(){return guardCondition;}
        public String getAction(){return action;}
        public String getEventCondition() {return eventCondition;}
        public String getFromStateName() {return fromStateName;}
        public String getToStateName() {return toStateName;}
        public String getTransTemplate() {return transTemplate;}
        public String getTriggerEvent() {return triggerEvent;}
    }
}
