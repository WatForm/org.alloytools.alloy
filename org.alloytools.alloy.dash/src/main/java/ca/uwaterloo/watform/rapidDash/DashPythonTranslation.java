package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashInit;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashModule;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.*;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.mit.csail.sdg.alloy4.TableView.clean;
import static edu.mit.csail.sdg.ast.ExprBinary.Op.*;

import edu.mit.csail.sdg.alloy4.ConstList;

/**
 * Mutable; this class represents an Dash to Python translation module
 */

public class DashPythonTranslation {

    private DashModule dashModule;

    public List<Signature> signatures;
    public List<Relation> relations;
    public List<Event> allEnvEvents = new ArrayList<Event>();
    public State rootState = null;
    private Map<String, State> concStateMap;

    public class Signature {
        public String name;
        public String multiplicity;     // TODO: could delete this
        public boolean isSubset;
        public boolean isSubsig;
        public boolean isAbstract;
        public boolean hasChildSubsig;
        public int scope;
        public boolean isOne;
        public boolean isLone;
        public List<String> parentNames;
        public String parentName;
        public List<String> objectNames;
        public List<String> subsigNames;
        public List<Signature> subsigs;

        public Signature(Sig sig, BufferedReader br, List<Signature> allSigs) {
            this.name = clean(sig.label);
            this.multiplicity = setMultiplicity(sig);       // TODO: could delete this
            this.isSubset = sig.isSubset != null;
            this.isSubsig = sig.isSubsig != null && ((Sig.PrimSig) sig).parent != Sig.UNIV;
            this.isAbstract = sig.isAbstract != null;
            this.isOne = sig.isOne != null;
            this.isLone = sig.isLone != null;

            // get parent names
            this.parentNames = (sig instanceof Sig.SubsetSig)? ((Sig.SubsetSig) sig).parents.stream().map(elem -> clean(elem.label)).collect(Collectors.toList()) : new ArrayList<>();
            this.parentName = (this.isSubsig)? clean(((Sig.PrimSig) sig).parent.label) : "";

            // list of subsigs
            this.subsigNames = new ArrayList<>();
            this.subsigs = new ArrayList<>();
            for(Signature otherSig : allSigs){
                if(otherSig.isSubsig && otherSig.parentName.equals(name)){
                    this.subsigs.add(otherSig);
                    this.subsigNames.add(otherSig.name);
                }
            }
            this.hasChildSubsig = !this.subsigNames.isEmpty();

            // calculating objects (strings) and the final scope
            this.objectNames = new ArrayList<>();
            scope = getScopes(sig, this.objectNames.size(), br);
            if(isSubset) {
                // subset signatures will always take objects in its "parents"
                for (Signature otherSig : allSigs){
                    // TODO: might want to add some non-determinism here:
                    // since there are multiple possible sets of objects for a subset
                    // currently, we are only filling in the subset in a "fixed" way
                    if(parentNames.contains(otherSig.name)){
                        if(otherSig.objectNames.size() < (scope - this.objectNames.size())){
                            this.objectNames.addAll(otherSig.objectNames);
                        }else{
                            for(int i = this.objectNames.size(), j = 0; i < scope; i++, j++){
                                this.objectNames.add(otherSig.objectNames.get(j));
                            }
                            break;
                        }
                    }
                }
            }else{
                // regular signatures
                int sum_children_scope = 0;
                if(hasChildSubsig){
                    if(isLone) {
                        // assume the Alloy model is correct, then there will only be at most 1 One subsig and multiple Lone subsig
                        // if One sig exists, make this Lone sig in fact a One sig
                        for (Signature subsig : this.subsigs) {
                            if (subsig.isOne) {
                                this.objectNames.addAll(subsig.objectNames);
                                break;
                            }
                        }
                    }else{
                        if(isAbstract && !isLone && !isOne){
                            for(Signature subsig : this.subsigs){
                                this.objectNames.addAll(subsig.objectNames);
                            }
                        }else{
                            // TODO: might want to add some non-determinism:
                            // since there could be multiple subsigs for this signature
                            // currently, we are only filling in the signature in a "fixed" way
                            for(Signature subsig : this.subsigs){
                                sum_children_scope += subsig.scope;
                                if(subsig.objectNames.size() < (scope - this.objectNames.size())){
                                    this.objectNames.addAll(subsig.objectNames);
                                }else{
                                    for(int i = this.objectNames.size(), j = 0; i < scope; i++, j++){
                                        this.objectNames.add(subsig.objectNames.get(j));
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
                // add more elements if not reached the scope required
                if(!isAbstract){
                    for(int i = sum_children_scope; i < scope; i++) {
                        this.objectNames.add(name + "$" + i);
                    }
                }
            }
            this.objectNames.sort(Comparator.comparing(item -> item));
            scope = this.objectNames.size();
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

        private int getScopes(Sig sig, int minimal_size, BufferedReader br) {
            if(isLone){return 0;}
            if(isOne){return 1;}
            if(sig.isSome != null){
                minimal_size = 1;
            }else if(minimal_size < 0){
                minimal_size = 0;
            }
            String input;
            while(true){
                // TODO: check the value for subsig/subset
                // scope of the subsig/subset should not exceed the scope of its parent(s)
                // TODO: add default in the future (and or change this part to be reading from a config file)
                // System.out.printf("Choose a scope for %s, (type \"d\" for default):%n", clean(sig.label));
                if(minimal_size != 0){
                    System.out.printf("Choose a scope for %s (at least %d, input < %d will be seen as %d):%n", clean(sig.label), minimal_size, minimal_size, minimal_size);
                }else{
                    System.out.printf("Choose a scope for %s (at least 0):%n", clean(sig.label));
                }
                try{
                    input = br.readLine();
                    int val = Integer.parseInt(input);
                    if(val < minimal_size){
                        val = minimal_size;
                    }
                    return val;
                } catch(NumberFormatException ex){
                    System.out.print("Please input a number! ");
                } catch (Exception ex){
                    System.out.print(ex);
                }
            }
        }
        public String getName() { return name; }
        public String getMultiplicity() { return multiplicity; }    // TODO: could delete this
        public String getParentName() {
            if (this.parentName != null)
                return this.parentName;
            return "";
        }
        public String getParentsName() {return String.join(", ", this.parentNames);}
        public List<String> getParentNames() {return this.parentNames;}
        public List<String> getSubsigNames() {return this.subsigNames;}
        public String getObjectNames() {
            if(this.objectNames.isEmpty()){
                return "";
            }
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
        public void addObject(String objName) {
            this.objectNames.add(objName);
            this.scope++;
        }
        public boolean isSubsig() {return isSubsig;}
        public boolean isSubset() {return isSubset;}
        public boolean isAbstract() {return isAbstract;}
        public boolean hasChildSubsig() {return hasChildSubsig;}
    }

    public class Relation {
        public String name;
        public String types;

        public Relation(String name, String types) {
            this.name = name;
            this.types = types;
        }

        public String getName() { return name; }
        public String getTypes() { return types; }
    }

    private String fieldDeclExprToString(Expr expr) {
        if (expr instanceof ExprVar) {
            return ((ExprVar) expr).label;
        } else if (expr instanceof ExprUnary) {
            return ((ExprVar) ((ExprUnary) expr).sub).label;
        } else if (expr instanceof ExprBinary) {
            if (!((ExprBinary) expr).op.isArrow) {
                // TODO: need to support union operator too.
                throw new ErrorFatal("Cannot handle operators other than arrow in field declarations");
            }
            return fieldDeclExprToString(((ExprBinary) expr).left) + ", " + fieldDeclExprToString(((ExprBinary) expr).right);
        }
        return "";
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

        // Sort the signatures based on dependencies (sort the list of signatures in topological order)
        List<Sig> signaturesOriginalList = new ArrayList<Sig>(dashModule.sigs.values());
        List<Sig> signaturesSortedList = topoSortSig(signaturesOriginalList);
        // subsigs <- sigs <- subsets

        // TODO: read a config file for this dash model, if exists
        // TODO: if no config file exists, read from user input and generate a config file
        // get signatures
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        this.signatures = new ArrayList<>();
        for(Sig sig : signaturesSortedList) {
            this.signatures.add(new Signature(sig, br, this.signatures));
        }

        // sort the signatures again, so it is in the same order as the input dash file
        Collections.sort(this.signatures, Comparator.comparing(item -> {
            for(int i = 0; i < signaturesOriginalList.size(); i++){
                if(item.name.equals(clean(signaturesOriginalList.get(i).label))){
                    return i;
                }
            }
            return -1;
        }));

        // get relations
        this.relations = new ArrayList<>();

        Set<Sig> keys = dashModule.old2fields.keySet();
        for (Sig key : keys) {
            // TODO: to filter out snapshot relations for now, might need to handle utility later
            if (dashModule.sigs.containsValue(key)){
                for (Decl decl : dashModule.old2fields.get(key)) {
                    String types = "[" + clean(key.label) + ", " + fieldDeclExprToString(decl.expr) + "]";
                    for (int i = 0; i < decl.names.size(); i++) {
                        relations.add(new Relation(((ExprVar) decl.names.get(i)).label, types));
                    }
                }
            }
        }

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
        	for(DashConcState substate: state.getInnerConcStates()) {
        		this.concStateMap.get(state.getFullyQualName()).addSubstate(this.concStateMap.get(substate.getFullyQualName()));
        		this.concStateMap.get(substate.getFullyQualName()).parent = concStateMap.get(state.getFullyQualName());
        	}
        	for(DashState substate: state.getInnerORStates()) {
        		this.concStateMap.get(state.getFullyQualName()).addSubstate(this.concStateMap.get(substate.getFullyQualName()));
        		this.concStateMap.get(substate.getFullyQualName()).parent = concStateMap.get(state.getFullyQualName());
        		if(substate.isDefault() && this.concStateMap.get(state.getFullyQualName()).defaultSubstate == null) {
        			this.concStateMap.get(state.getFullyQualName()).defaultSubstate = this.concStateMap.get(substate.getFullyQualName());
        		}
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

    private void dfs(List<Sig> outputList, Set<String> covered, Set<Sig> subsets, Sig sig){
        if(covered.contains(clean(sig.label))){
            return;
        }
        if(sig instanceof Sig.PrimSig && ((Sig.PrimSig) sig).parent != null) {
            dfs(outputList, covered, subsets, ((Sig.PrimSig) sig).parent);
            outputList.add(sig);
        }else if(sig instanceof Sig.SubsetSig && ((Sig.SubsetSig) sig).parents != null){
            subsets.add(sig);
        }
        covered.add(clean(sig.label));
    }
    private List<Sig> topoSortSig(List<Sig> list){
        Deque<Sig> signaturesOriginalQueue = new ArrayDeque<Sig>(list);
        List<Sig> signaturesSortedList = new ArrayList<Sig>();
        Set<String> covered = new HashSet<String>();
        Set<Sig> subsets = new HashSet<Sig>();
        while (signaturesOriginalQueue.size() != 0) {
            Sig sig = signaturesOriginalQueue.pop();
            dfs(signaturesSortedList, covered, subsets, sig);
        }
        Collections.reverse(signaturesSortedList);
        signaturesSortedList.addAll(subsets);
        return signaturesSortedList;
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
