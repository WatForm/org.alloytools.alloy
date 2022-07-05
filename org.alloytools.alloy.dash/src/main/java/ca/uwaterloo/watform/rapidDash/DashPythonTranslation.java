package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashModule;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
        public boolean isSubset;
        public boolean isSubsig;
        public boolean isAbstract;      // TODO: might not need this
        public boolean hasChildSubsig;
        public int scope;
        public List<String> parentNames;
        public String parentName;
        public List<String> objectNames;
        public List<Integer> bounds;
        public List<String> subsigNames;

        public Signature(Sig sig, int scope, ArrayList<Sig> allSigs) {
            this.name = clean(sig.label);
            this.multiplicity = setMultiplicity(sig);
            this.isSubset = sig.isSubset != null;
            this.isSubsig = sig.isSubsig != null && ((Sig.PrimSig) sig).parent != Sig.UNIV;
            this.isAbstract = sig.isAbstract != null;
            this.scope = scope;

            // get parent names
            this.parentNames = new ArrayList<>();
            if (sig.isSubset != null)
                for (Sig p : ((Sig.SubsetSig) sig).parents)
                    this.parentNames.add(clean(p.label));

            if (this.isSubsig)
                this.parentName = clean(((Sig.PrimSig) sig).parent.label);

            // possible objects (strings)
            this.objectNames = new ArrayList<>();
            if(!isSubset){
                for(int i = 0; i < scope; i++){
                    this.objectNames.add(name + "$" + (i+1));
                }
            }

            // list of subsigs
            this.subsigNames = new ArrayList<>();
            for(Sig otherSig : allSigs){
                if(otherSig.isSubsig != null && clean(((Sig.PrimSig) otherSig).parent.label).equals(this.name)){
                    this.subsigNames.add(clean(otherSig.label));
                }
            }
            this.hasChildSubsig = !this.subsigNames.isEmpty();

            // constraint on size
            this.bounds = new ArrayList<>();
            this.bounds.add(0);           // TODO: what if scope doesn't start from 0?
            this.bounds.add(scope);
        }

        private String setMultiplicity(Sig sig) {
            if (sig.isLone != null)
                return "lone";
            if (sig.isOne != null)
                return "one";
            if (sig.isSome != null)
                return "some";
            return "set";
        }

        public String getName() { return name; }
        public String getMultiplicity() { return multiplicity; }
        public int getCardinality() { return scope; }
        public String getParentName() {
            if (this.parentName != null)
                return this.parentName;
            return "";
        }
        public String getParentsName() {return String.join(", ", this.parentNames);}
        public List<String> getParentNames() {return this.parentNames;}
        public List<String> getSubsigNames() {return this.subsigNames;}
        public String getObjectNames() {
            StringJoiner joiner = new StringJoiner("\", \"", "\"", "\"");
            for (CharSequence cs: this.objectNames) {
                joiner.add(cs);
            }
            return joiner.toString();
        }
        public void addObjects(List<String> objName) {
            this.objectNames.addAll(objName);
            this.scope += objName.size();
        }

        public boolean isSubsig() {return isSubsig;}
        public boolean isSubset() {return isSubset;}
        public boolean isAbstract() {return isAbstract;}
        public boolean hasChildSubsig() {return hasChildSubsig;}
        public int getLowerBound() {return bounds.get(0);}
        public int getUpperBound() {return bounds.get(1);}
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

        // TODO: read a config file for this model if exists
        // TODO: if no config file exists, read from user input and generate a config file
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        // get signatures
        this.signatures = new ArrayList<>();
        for(Sig sig : signaturesSortedList){
            this.signatures.add(new Signature(sig, getScopes(sig, br), signaturesSortedList));
        }

        // get state hierarchy
        this.concStateMap = new HashMap<>();
        // initialize all states instances
        for(String stateName: dashModule.concStates.keySet()){
            this.concStateMap.put(stateName, new State(stateName, true));
        }
        for(String stateName: dashModule.states.keySet()){
            this.concStateMap.put(stateName, new State(stateName, false));
        }
        
        for(DashConcState state: dashModule.concStates.values()) {
        	if(rootState == null) {
        		rootState = this.concStateMap.get(state.modifiedName);
        	}
        	// add state variable declarations (decls)
        	for(Decl decl: state.decls) {
        		DashExprToPython dashExprTranslator = new DashExprToPython<>(decl.expr);
        		dashExprTranslator.isDecl = true;
        		this.concStateMap.get(state.modifiedName).addDecl("self." + decl.get() + " = " + dashExprTranslator.toString());
        	}
        	// add state variable initializations and constraints (inits and init_constraints)
        	for(DashInit init: state.init) {
        		for(Expr expr: init.exprList) {
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
        					this.concStateMap.get(state.modifiedName).addInitConstraint("assert " + dashExprTranslator.toString());
        					continue;
        				}
        			}
            		this.concStateMap.get(state.modifiedName).addInit(dashExprTranslator.toString());
        		}
        	}
        	
        	// add state events
        	for(DashEvent event: state.events) {
        		Event newEvent = new Event(event.name, event.modifiedName, event.type, this.concStateMap.get(state.modifiedName));
        		this.concStateMap.get(newEvent);
        		if(newEvent.isEnvEvent) {
        			allEnvEvents.add(newEvent);
        		}
        	}
        	     	
        	// add substates to conc states
        	for(DashConcState substate: state.concStates) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        	}
        	for(DashState substate: state.states) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        		if(substate.isDefault && this.concStateMap.get(state.modifiedName).defaultSubstate == null) {
        			this.concStateMap.get(state.modifiedName).defaultSubstate = this.concStateMap.get(substate.modifiedName);
        		}
        	}
        }
        
        // add substates to dash states
        for(DashState state: dashModule.states.values()) {
        	for(DashState substate: state.states) {
        		this.concStateMap.get(state.modifiedName).addSubstate(this.concStateMap.get(substate.modifiedName));
        		this.concStateMap.get(substate.modifiedName).parent = concStateMap.get(state.modifiedName);
        	}
        }

        // generate transitions
        for(DashTrans dashTrans : dashModule.transitions.values()){
            Transition trans = new Transition(dashTrans);
            this.concStateMap.get(trans.getStateName()).addTransition(trans);
        }
    }

    private int getScopes(Sig sig, BufferedReader br) {
        if (sig.isOne !=null || sig.isLone != null){
            return 1;
        }
        String input;
        while(true){
            // TODO: check the value for subsig/subset
            // scope of the subsig/subset should not exceed the scope of its parent(s)
            // TODO: add default in the futrue (and or change this part to be reading from a config file)
            // System.out.printf("Choose a scope for %s, (type \"d\" for default):%n", clean(sig.label));
            System.out.printf("Choose a scope for %s:%n", clean(sig.label));
            try{
                input = br.readLine();
                return Integer.parseInt(input);
            } catch(NumberFormatException ex){
                System.out.print("Please input a number! ");
            } catch (Exception ex){
                System.out.print(ex);
            }
        }
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
        public State defaultSubstate = null;
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
        public State getDefaultSubstate() {
        	return defaultSubstate != null ? defaultSubstate : substates.get(0);
        }
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
            this.transName = dashTrans.name;
            if (dashTrans.parentState instanceof DashConcState) {
                this.stateName = ((DashConcState)dashTrans.parentState).modifiedName;
            } else {
                this.stateName = ((DashState)dashTrans.parentState).modifiedName;
            }

            // check keywords
            if(dashTrans.fromExpr != null){    // determines which state this transition belongs to
                this.fromStateName = dashTrans.fromExpr.fromExpr.get(0);
            }
            if(dashTrans.onExpr != null){      // determines the trigger event
                this.eventCondition = dashTrans.onExpr.name;
            }
            if(dashTrans.whenExpr != null){    // determines the guard_condition (if statement)
                DashExprToPython dashExprTranslator = new DashExprToPython<>(dashTrans.whenExpr);

                // set condition
                this.guardCondition = dashExprTranslator.toString();
            }
            if(dashTrans.doExpr != null){      // determines the action
                DashExprToPython dashExprTranslator = new DashExprToPython<>(dashTrans.doExpr);

                // set action
                this.action = dashExprTranslator.toString();
            }
            if(dashTrans.gotoExpr != null){    // determine the next state
                this.toStateName = dashTrans.gotoExpr.gotoExpr.get(0);
            }
            if(dashTrans.sendExpr != null){    // determines the event to send
                this.triggerEvent = dashTrans.sendExpr.name;
            }
            if(dashTrans.transTemplate != null){   // TODO: don't know what this does
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
