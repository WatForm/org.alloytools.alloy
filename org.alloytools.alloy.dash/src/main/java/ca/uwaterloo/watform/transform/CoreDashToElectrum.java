package ca.uwaterloo.watform.transform;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

// Dash Imports
import ca.uwaterloo.watform.ast.*;
import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;

// Alloy Imports
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Attr.*;
import edu.mit.csail.sdg.ast.Sig.*;

public class CoreDashToElectrum {
	private boolean isCreatingEnabledAfterPred;
	private boolean isCreatingInit;
	private boolean isCreatingExprQt;
	
	private Map <Integer, List<DashTrans>> eventSize2Trans;
	private Map<String, DashConcState> changedLocalVars; // Variables changed only locally
	private List<String> changedRefVars; // Variables changed by reference in the transitions being checked
	private Map<String, DashConcState> changedVars; // Keep a track of when a variable has been changed during a transition
	private boolean refParamChanged;

	private Map<String, Expr> paramBuffer;
	private Map<String, Expr> paramBufferChanged ;
	private Map<String, Expr> localBufferChanged ;
	// Buffer Helpers
	private List<String> bufferCommands;
	private List<String> bufferFuncCommands;
	// Changed parameterized buffers that are universally quantified (No need to keep this unchanged for other replicated processes since it is universally quantified for all elements in a set of Processes
	private boolean foundBuffer = false;
	
	public CoreDashToElectrum () {
		isCreatingEnabledAfterPred = false;
		isCreatingInit = false;
		isCreatingExprQt = false;
		refParamChanged = false;
		
		eventSize2Trans = new LinkedHashMap<Integer, List<DashTrans>>();
		changedLocalVars = new LinkedHashMap<String, DashConcState>();
		changedRefVars = new ArrayList<String>();
		changedVars = new LinkedHashMap<String, DashConcState>();
		paramBuffer = new LinkedHashMap<String, Expr>();
		paramBufferChanged = new LinkedHashMap<String, Expr>();
		localBufferChanged = new LinkedHashMap<String, Expr>();
		bufferCommands = Arrays.asList(new String[]{"addFirst", "add", "remove", "removeFirst"});
		bufferFuncCommands = Arrays.asList(new String[]{"firstElem"});
		foundBuffer = false;
	}

    public DashModule convertToElectrumAST(DashModule module, String fileName, String path) {	
    	DashModule alloyModule = new DashModule(module, fileName, path, true);
    	
    	convertCommand(alloyModule);
    	createrBufIdxSig(alloyModule);
    	createParamSigAST(alloyModule);
    	addStableSig(alloyModule);

        createStateSpaceAST(alloyModule);
        createEventSpaceAST(alloyModule);
        createTransitionSpaceAST(alloyModule);
        
        createTransitionsAST(alloyModule);
        
        createInitAST(alloyModule);
        createTestIfStableAST(alloyModule);
        createSmallStepAST(alloyModule);
        
        createEqualsAST(alloyModule);
        createElectrumTracesFact(alloyModule);

        createIsEnabledAST(alloyModule);
        //createInvariantFact(alloyModule);
        
        return alloyModule;
    }

    /**************************** CREATING ALL SIGNATURES *****************************/
    
    private void createrBufIdxSig (DashModule module) {
    	for (String bufIdx: module.bufferNameToIndex.values()) {
    		addSigAST(module, bufIdx, null, null, null, null, null, null, null, null);
    	}
    }

    private void createParamSigAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = null;
        
        // conf0: StateLabel
        // conf1: Identifier -> StateLabel
        for (int tupleSize: module.confTuples) {
        	if (tupleSize == 0) {
        		addVarSigAST(module, "conf0", ExprVar.make(null, "StateLabel"));
        		continue;
        	}
        	b = (tupleSize == 1) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "StateLabel")) : ExprVar.make(null, "StateLabel");
        	for (int i = 0; i < tupleSize - 1; i++) {
        		b = DashHelper.createBinaryExpr(ExprVar.make(null, "Identifiers"), ExprBinary.Op.ARROW, b);
        	}
        	a.add(ExprVar.make(null, "conf" + tupleSize));
        	decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
            a.clear();
        }
        
        // taken0: TransitionLabel
        // taken1: Identifier -> TransitionLabel
        for (int tupleSize: module.confTuples) {
        	if (tupleSize == 0) {
        		addVarSigAST(module, "taken0", ExprVar.make(null, "TransitionLabel"));
        		continue;
        	}
        	b = (tupleSize == 1) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "TransitionLabel")) : ExprVar.make(null, "TransitionLabel");
        	for (int i = 0; i < tupleSize - 1; i++) {
        		b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Identifiers"), b);
        	}
        	a.add(ExprVar.make(null, "taken" + tupleSize));
        	decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
            a.clear();
        }

        // events0: EventLabel
        // events1: Identifier -> EventLabel
        for (int tupleSize: module.eventTuples) {
        	if (tupleSize == 0) {
        		addVarSigAST(module, "events0", ExprVar.make(null, "EventLabel"));
        		continue;
        	}
        	b = (tupleSize == 1) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "EventLabel")) : ExprVar.make(null, "EventLabel");
        	for (int i = 0; i < tupleSize - 1; i++) {
        		b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Identifiers"), b);
        	}
        	a.add(ExprVar.make(null, "events" + tupleSize));
        	decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
            a.clear();
        }
        
        addSigAST(module, "Identifiers", null, null, new ArrayList<Decl>(decls), null, null, null, null, null);
        decls.clear();
        
        for (DashConcState concState: module.concStates.values()) {
        	if (concState.getIdentifiers().size() > 0) {
                /* Creating the following expression: variable: mappings (variable: param -> mapping if parameterized)*/
                for (String variableName : module.variable2Expression.keySet()) {
                	if (!module.variable2ConcState.get(variableName).getFullyQualName().equals(concState.getFullyQualName())) continue;       		
                    b = module.variable2Expression.get(variableName);
                    b = DashHelper.createParameterizedElectrumVar(variableName, b, module);
                    a.add(ExprVar.make(null, variableName));
                	decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, convertToExprUnary(b)));              
                    a.clear();
                }
                addSigAST(module, concState.getReplicatedIdentifier(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "Identifiers"))), new ArrayList<Decl>(decls), null, null, null, null, null);
                decls.clear();
        	}
        }
        
        // Creating the Variable signature and its relations
        decls.clear();
        for (String variableName : module.variable2Expression.keySet()) {
        	if (module.variable2ConcState.get(variableName).getIdentifiers().size() > 0) continue;       		
            b = module.variable2Expression.get(variableName);
            b = DashHelper.createParameterizedVar(variableName, b, module);
            a.add(ExprVar.make(null, variableName));
        	decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, convertToExprUnary(b))); 
            a.clear();
        }
        addSigAST(module, "Variables", null, null, new ArrayList<Decl>(decls), null, null, new Pos("one", 0, 0), null, null);
    }

    /* Used by other functions to help create signature ASTs */
    private void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));
    }
    
    private void addVarSigAST(DashModule module, String sigName, ExprVar sigParent) {
        module.addSig(sigName, ExprVar.make(null, "in"), new ArrayList<ExprVar>(Arrays.asList(sigParent)), null, null, null, AttrType.ABSTRACT.makenull(null), AttrType.LONE.makenull(null), AttrType.ONE.makenull(null), AttrType.SOME.makenull(null), AttrType.PRIVATE.makenull(null), AttrType.VARIABLE.makenull(new Pos(sigParent.toString(), 0, 0)));
    }
    
    private void addStableSig(DashModule module) {
        module.addSig("stable", ExprVar.make(null, "in"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "Bool"))), null, null, null, AttrType.ABSTRACT.makenull(null), AttrType.LONE.makenull(null), AttrType.ONE.makenull(null), AttrType.SOME.makenull(null), AttrType.PRIVATE.makenull(null), AttrType.VARIABLE.makenull(new Pos("Bool", 0, 0)));    
    }

    /****************************************** STATE SPACE ***************************************/
    
    /* Create the following expression: 
	       abstract sig SystemState extends StateLabel {}
		   abstract sig System extends SystemState {}
		   one sig State_Name extends System {}
		   ...
     */
    private void createStateSpaceAST(DashModule module) {
    	addSigAST(module, "StateLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "SystemState", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "StateLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);

        for (DashConcState concState : module.topLevelConcStates.values()) {
        	if(concState.getInnerConcStates().size() > 0)
        		addSigAST(module, concState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else if(concState.getInnerORStates().size() > 0)
        		addSigAST(module, concState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	else
        		addSigAST(module, concState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "SystemState"))), new ArrayList<Decl>(), null, null,  new Pos("one", 0, 0), null, null);
        	
            createStateAST(concState, module);
        }
    }

    private void createStateAST(DashConcState concState, DashModule module) {
        for (DashState state : concState.getInnerORStates()) {
        	if(state.getInnerORStates().size() == 0 && state.getInnerConcStates().size() == 0) {
        		addSigAST(module, state.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.getFullyQualName()))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        		createChildStateAST(state, module);
        	}
        	else {
        		addSigAST(module, state.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.getFullyQualName()))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        		createChildStateAST(state, module);
        	}
        }

        for (DashConcState innerConcState : concState.getInnerConcStates()) {
            addSigAST(module, innerConcState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, concState.getFullyQualName()))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
            createStateAST(innerConcState, module);
        }
    }
    
    private void createChildStateAST(DashState state, DashModule module) {
        for(DashState innerState: state.getInnerORStates()) {
        	if(innerState.getInnerORStates().size() == 0 && innerState.getInnerConcStates().size() == 0) {
        		addSigAST(module, innerState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.getFullyQualName()))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        	}
        	else {
        		addSigAST(module, innerState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.getFullyQualName()))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        		createChildStateAST(innerState, module);
        	}
        }
        
        for (DashConcState concState: state.getInnerConcStates()) {
        	if (concState.getInnerORStates().size() > 0) {
        		addSigAST(module, concState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.getFullyQualName()))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        	}
        	else {
        		addSigAST(module, concState.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, state.getFullyQualName()))), new ArrayList<Decl>(), new Pos("one", 0, 0), null, null, null, null);
        	}
        	createStateAST(concState, module);
        }
    }
    
    /****************************************** EVENT SPACE ***************************************/

    private void createEventSpaceAST(DashModule module) {
    	addSigAST(module, "EventLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "EnvironmentEvent", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EventLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        addSigAST(module, "InternalEvent", ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EventLabel"))), new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
    	
        for (String key : module.events.keySet()) {
            if (module.events.get(key).type.equals("env event"))
            	addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            if (module.events.get(key).type.equals("event"))
            	addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "InternalEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }
    
    /****************************************** TRANSITION SPACE ***************************************/


    private void createTransitionSpaceAST(DashModule module) {
    	addSigAST(module, "TransitionLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        for (DashTrans transition : module.transitions.values()) {
        	addSigAST(module, transition.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "TransitionLabel"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }
    
    /****************************************** CREATE TRANSITIONS (PRE, POST, SEMANTICS, ENABLEDAFTERSTEP) ***************************************/
    
    private void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.transitions.values()) {
            createPreConditionAST(transition, module);
            createPostConditionAST(transition, module);
            createTransCallAST(transition, module);
            createEnabledNextStepAST(transition, module);
            createSemanticsAST(transition, module);
        }
    }
    
    /****************************************** PRE CONIDTION PREDICATE ***************************************/
    
    /*
     * This function creates the AST for the precondition predicate in the Alloy
     * Model
     */
    private void createPreConditionAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        expression = ExprUnary.Op.NOOP.make(null, getPreCondAST(transition, module));
        addTransitioPredicate(module, "pre_" + transition.getFullyQualName(), transition.getParentConcState().getIdentifiers(), expression);
    }

    /*
     * Create the pre-conditions AST and returns it. Is used both for creating the
     * pre-cond predicate and for adding pre-conditions to the
     * enabledAfterStep_transName predicate
     */
    private Expr getPreCondAST(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST
        Expr binaryFrom = null;
		int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();
        /* Creating the following expression: sourceState in s.conf */
        if (transition.getOrigin().fromExpr.size() > 0) {       
            Expr left = null;
        	for(DashState state: module.states.values()){
    			String fromState = transition.getOrigin().fromExpr.get(0).replace('/', '_');
        		if(state.getInnerORStates().size() > 0 && state.getFullyQualName().equals(transition.getOrigin().fromExpr.get(0).replace('/', '_'))) {
        			left =  DashHelper.createExprVar(fromState); 
        			Expr right = DashHelper.conf(totalIEsInTree);
        			right = DashHelper.addParametersJoin(right, totalIEsInTree);
        			binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.INTERSECT, mult(right));
        			binaryFrom = DashHelper.createUnaryExpr(ExprUnary.Op.SOME, binaryFrom);     				
        			break;
        		}
        		else if(state.getInnerORStates().size() == 0 && state.getFullyQualName().equals(transition.getOrigin().fromExpr.get(0).replace('/', '_'))){
        			left =  DashHelper.createExprVar(fromState); 
        			Expr right = DashHelper.conf(totalIEsInTree);
        			right = DashHelper.addParametersJoin(right, totalIEsInTree);
                    binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(right));
        			break;
        		}     			
        	}
        	if(binaryFrom == null) {
        		Expr right = DashHelper.conf(totalIEsInTree);
        		Expr source = DashHelper.createExprVar(transition.getOrigin().fromExpr.get(0).replace('/', '_')); 
        		binaryFrom = DashHelper.createBinaryExpr(source, ExprBinary.Op.IN,  mult(right));
        	}
        }

        /*
         * Creating the following expression: onExprName in (s.events &
         * EnvironmentEvent)
         */
        Expr binaryOn = null;
        
        String onCommand = transition.onExpr == null ? "" : transition.onExpr.getRawName().replace('/', '_');
        int iesInEvent = (transition.onExpr != null) ? transition.onExpr.getParentConcState().getIdentifiers().size() : 0;
        if (transition.onExpr != null && transition.onExpr.getRawName() != null && module.isEnvEventModel && !module.stateHierarchy) {
        	Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.events(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent); // p0.(s.events)
            Expr rightBinary = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, DashHelper.envEvent()); // events & EnvironmentEvent
            binaryOn = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(rightBinary)); //ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (events & EnvironmentEvent)         
        }
        
        if (transition.onExpr != null && transition.onExpr.getRawName() != null && transition.onExpr.isInternal && module.isEnvEventModel && module.stateHierarchy) {
        	Expr sStableTrue = DashHelper.createBinaryExpr(DashHelper.stable(), ExprBinary.Op.EQUALS, DashHelper.trueExpr()); // stable = True
        	Expr notSStableTrue = DashHelper.createUnaryExpr(ExprUnary.Op.NOT, sStableTrue); // !(s.stable = True)
            Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.events(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent);
            Expr eventInSEvents = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(sEvents));  //onExprName in (s.events)  
            binaryOn = ExprBinary.Op.OR.make(null, null, notSStableTrue, eventInSEvents); // !(s.stable = True) or onExprName in (s.events)          
        }
        else if (transition.onExpr != null && transition.onExpr.getRawName() != null && module.isEnvEventModel && module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, DashHelper.stable(), ExprVar.make(null, "True"));
            Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.events(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent);
            Expr rightBinary = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, DashHelper.envEvent()); // s.events & EnvironmentEvent
            Expr ifExpr = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)
            Expr elseExpr = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(sEvents)); //onExprName in (s.events)  
            binaryOn = ExprITE.make(null, sStableTrue, ifExpr, elseExpr);             
        }

        expression = (binaryOn != null) ? ExprBinary.Op.AND.make(null, null, binaryFrom, binaryOn) : binaryFrom;

        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {        	
            Expr modifiedExpr = getVarFromParentExpr(transition.whenExpr.expr, getParentConcState(transition.getParent()), module);
            expression = (expression == null) ? ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr) : ExprBinary.Op.AND.make(null, null, expression, modifiedExpr); 
        }

        return expression;
    }
    
    private Expr getPreCondForEnabled(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST
		int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();
        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf (if no inner OR states)
         * else create: some sourceState in s.conf */
        if (transition.getOrigin().fromExpr.size() > 0) {       
            Expr left = null;
            
        	DashState sourceState = DashHelper.getState(transition.getOrigin().fromExpr.get(0), module);
        	String fromExprStr = transition.getOrigin().fromExpr.get(0).replace('/', '_');
        	
        	if(sourceState != null && sourceState.getInnerORStates().size() > 0) {
        		left = ExprVar.make(null, fromExprStr);
        		Expr right = DashHelper.confPrimed(totalIEsInTree);
    			right = DashHelper.addParametersJoin(right, totalIEsInTree);
    			binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.INTERSECT, mult(right));
    			binaryFrom = DashHelper.createUnaryExpr(ExprUnary.Op.SOME, binaryFrom); 
        	}
        	else if(sourceState != null && sourceState.getInnerORStates().size() == 0){
                left = ExprVar.make(null, fromExprStr);
                Expr right = DashHelper.confPrimed(totalIEsInTree);
    			right = DashHelper.addParametersJoin(right, totalIEsInTree);
                binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(right));
        	}     			
        	
        	if(binaryFrom == null) {
        		Expr right = DashHelper.confPrimed(totalIEsInTree);
        		right = DashHelper.addParametersJoin(right, totalIEsInTree);
        		Expr source = ExprVar.make(null, fromExprStr);
        		binaryFrom = ExprBinary.Op.IN.make(null, null, source, mult(right));
        	}	
        }

        expression = binaryFrom;

        isCreatingEnabledAfterPred = true;
        
        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.whenExpr != null && transition.whenExpr.exprList != null) {           	
            Expr modifiedExpr = getVarFromParentExpr(transition.whenExpr.expr, getParentConcState(transition.getParent()), module);
            expression = (expression == null) ? ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr) : ExprBinary.Op.AND.make(null, null, expression, modifiedExpr); 
        }

        isCreatingEnabledAfterPred = false;

        return expression;
    }
    
    /****************************************** POST CONDITION PREDICATE ***************************************/

    /*
     * This function creates the AST for the postcondition predicate in the Alloy
     * Model
     */
    private void createPostConditionAST(DashTrans transition, DashModule module) {
    	//System.out.println("\nTransition: " + transition.getFullyQualName());
    	DashConcState parent = getParentConcState(transition.getParent());
    	Expr sendExpr = null;
        Expr expression = null;
		int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();

        /*
         * Creating the following expression: s_next.conf = s.conf - sourceState +
         * destinationState
         */
        if (transition.gotoExpr.gotoExpr.size() > 0) {
        	String gotoExprStr = transition.gotoExpr.getAlloyName();         
        	
            String fromExprStr = (DashHelper.getState(transition.getOrigin().getAlloyName(), module) != null) ? DashHelper.getState(transition.getOrigin().getAlloyName(), module).getFullyQualName() : transition.getOrigin().getAlloyName();;
            //fromExprStr = (DashHelper.getState(transition.getOrigin().getAlloyName(), module) != null) ? DashHelper.getState(transition.getOrigin().getAlloyName(), module).getFullyQualName() : transition.getOrigin().getAlloyName();
           
            Expr fromExpr = ExprVar.make(null, fromExprStr);
            Expr gotoExpr = ExprVar.make(null, gotoExprStr);
        	gotoExpr = DashHelper.addParametersArrow(gotoExpr, totalIEsInTree);
            fromExpr = DashHelper.addParametersArrow(fromExpr, totalIEsInTree);
        	Map<Integer, Expr> conf2GotoExpr = new LinkedHashMap<Integer, Expr>();
        	Map<Integer, Expr> conf2FromExpr = new LinkedHashMap<Integer, Expr>();
            
            /* If we are transitioning into a state with concurrent states */
            if (transition.gotoExpr.gotoExprs != null && transition.gotoExpr.gotoExprs.size() > 0) {
            	conf2GotoExpr = new LinkedHashMap<Integer, Expr>(DashHelper.calculateConf2GotoExpr(transition));
            }
            
            /* If we are transitioning out of a concurrent state */
            if (transition.getOrigin().fromExprs != null && transition.getOrigin().fromExprs.size() > 0) {
            	conf2FromExpr = new LinkedHashMap<Integer, Expr>(DashHelper.calculateConf2FromExpr(transition));
            }
            
            /* s_next.conf0 = (s.conf0 + .... ) and
             * s_next.conf1 = (s.conf1 + .... ) and
             * ... */
            for (int i: module.confTuples) {
                Expr sConf = DashHelper.conf(i);//conf
                Expr sConfPrime = DashHelper.confPrimed(i);//conf'
                
                // s.conf - (p0 -> State)
                sConf = !(transition.getOrigin().leavingMultipleStates) && (totalIEsInTree == i) ? DashHelper.createBinaryExpr(sConf, ExprBinary.Op.MINUS, fromExpr) : sConf;
                // s.conf + (p0 -> State)
                sConf = !(transition.gotoExpr.enteringDefaultStates) && (totalIEsInTree == i) ? DashHelper.createBinaryExpr(sConf, ExprBinary.Op.PLUS, gotoExpr) : sConf;
                
                if (conf2FromExpr.containsKey(i)) {
                	sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.MINUS, conf2FromExpr.get(i)); //s.conf - (IE -> State)
                }
                if (conf2GotoExpr.containsKey(i)) {
                	sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.PLUS, conf2GotoExpr.get(i)); //s.conf + (IE -> State)
                }
                sConfPrime = DashHelper.createBinaryExpr(sConfPrime, ExprBinary.Op.EQUALS, sConf); // s_next.conf = s.conf - ... + ...
                expression = (expression == null) ? sConfPrime : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sConfPrime);
            }
        }

        /* Creating the following expression: AND[doexpr, doexpr, ..] i.e Printing out the actions */
        if (transition.doExpr != null && transition.doExpr.exprList != null) {                    
            Expr modifiedExpr = getVarFromParentExpr(transition.doExpr.expr, getParentConcState(transition.getParent()), module);                 
            expression =  DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, modifiedExpr); // ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            Map<String, DashConcState> unchangedVars = new LinkedHashMap<String, DashConcState>(getUnchangedVars(transition.doExpr.exprList, module));
            for (String var: changedLocalVars.keySet()) {
            	// We dont constrain a var if it has been changed using a reference, otherwise we constrain it if it only has been changed locally
            	expression = (changedRefVars.contains(var) || (changedLocalVars.get(var).getIdentifiers().size() == 0) ) ? expression : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, constrainLocallyChangedVars(var, changedLocalVars.get(var))); // ExprBinary.Op.AND.make(null, null, expression, constrainLocallyChangedVars(var, parent));
            }
            for (String var : unchangedVars.keySet()) {
                expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, createUnchangedVariableAST(var, unchangedVars.get(var), parent)); //ExprBinary.Op.AND.make(null, null, expression, createUnchangedVariableAST(var, unchangedVars.get(var), parent));
            }
            clearVarChangeContainers();
        }
        
        /* Creating the following expression(s): s_next.variable = s.variable 
         * Keeping variables unchanged */
        if (transition.doExpr == null) {
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            Map<String, DashConcState> unchangedVars = new LinkedHashMap<String, DashConcState>(getUnchangedVars(null, module));
            for (String var : unchangedVars.keySet()) {
                expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, createUnchangedVariableAST(var, unchangedVars.get(var), parent));
            }
            changedVars.clear();
        }

        /****************************************** TEST IF STABLE CALL ****************************************************/
        /*
         * Creating the following expression: testIfNextStable[s, s_next, {none},
         * Mutex_Process1_wait] => { s_next.stable = True } else { s_next.stable = False }
         */
        if (module.stateHierarchy && !module.isEnvEventModel) {
        	Expr sNextStable =  DashHelper.stablePrimed();
        	Expr ifExpr = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr());
            Expr ElseExpr = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.falseExpr());
            Expr ifCond = DashHelper.createExprVar("testIfNextStable"); 
            ifCond = DashHelper.createExprBadJoin(transition.getFullyQualName(), ifCond);
            ifCond =DashHelper.createExprBadJoin("none", ifCond);
            
            /* Conjunction of any env variables in the model */
            for(String concStateName: module.envVariableNames.keySet()) {
            	for(String envVar: module.envVariableNames.get(concStateName)) {
            		Expr primedVar = DashHelper.varPrimed(concStateName + "_" + envVar);
            		Expr leftJoin = primedVar;
            		Expr rightJoin = DashHelper.createExprVar(concStateName + "_" + envVar);
            		Expr equals = DashHelper.createBinaryExpr(leftJoin, ExprBinary.Op.EQUALS, rightJoin);
            		ElseExpr = DashHelper.createBinaryExpr(ElseExpr, ExprBinary.Op.AND, equals); //ExprBinary.Op.AND.make(null, null, ElseExpr, equals);
            	}
            }
            
            Expr ifElseExpr = DashHelper.createImplesElseExpr(ifCond, ifExpr, ElseExpr); //ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, ifElseExpr); //ExprBinary.Op.AND.make(null, null, expression, ifElseExpr);
        }
        
        /*
         * Creating the following expression: testIfNextStable[s, s_next, {none},
         * Elevator_Controller_sendReq] => { s_next.stable = True s.stable = True => { no
         * ((s_next.events & InternalEvent) ) } else { no ((s_next.events & InternalEvent) - {
         * (InternalEvent & s.events)}) } } else { s_next.stable = False s.stable = True =>
         * { s_next.events & InternalEvent = {none}/sendExpr s_next.events & EnvironmentEvent = s.events
         * & EnvironmentEvent } else { s_next.events = s.events + {none}/sendExpr } }
         */
        if (module.stateHierarchy && module.isEnvEventModel) {
        	String sendCommand = transition.sendExpr == null ? "" : transition.sendExpr.getRawName().replace('/', '_');
        	int iesInEvent = transition.sendExpr != null ? transition.sendExpr.getParentConcState().getIdentifiers().size() : 0;
        	Expr sNextStable = DashHelper.stablePrimed();
        	Expr sPrimeStableTrue = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr()); //s_next.stable = True
        	Expr sPrimeStableFalse = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.falseExpr()); //s_next.stable = False
           
            Expr sStableTrue = DashHelper.createBinaryExpr(DashHelper.stable(), ExprBinary.Op.EQUALS,  DashHelper.trueExpr()); //s.stable = False
            
            if(transition.sendExpr != null && transition.sendExpr.getRawName() != null) {
            	if(transition.sendExpr.param != null) {
            		sendExpr = DashHelper.createBinaryExpr(getVarFromParentExpr(transition.sendExpr.param, transition.sendExpr.getParentConcState(), module), ExprBinary.Op.ARROW, DashHelper.createExprVar(sendCommand));
            		sendExpr = DashHelper.addParametersArrow(sendExpr, iesInEvent - 1);
            	}
            	else {
            		sendExpr = DashHelper.createExprVar(sendCommand);
            		sendExpr = DashHelper.addParametersArrow(sendExpr, iesInEvent);
            	}
            }
            
            Expr ifLowerExpr = null;
            Expr elseLowerExpr = null;
            Expr sPrimeEnvAndIntEvnEqualsEvn = null;
            Expr sPrimeEvnIntEvnEqualsSend = null;
            Expr sNextEvnEqlSEnv = null;
            Expr sEnvEqEnvPlusSend = null;
            Expr sendExprCom = null;
            for (int key: module.eventTuples) {
            	Expr noneToNone = DashHelper.addIdentifiersNone(DashHelper.createExprVar("none"), key);
            	sendExprCom = (key == iesInEvent) ? sendExpr : noneToNone;
            	sendExprCom = (sendExprCom == null) ? noneToNone : sendExprCom;
            	Expr intEvent = DashHelper.intEvent();
            	intEvent = DashHelper.addIdentifiersArrow(intEvent, key);
                Expr sEvents = DashHelper.events(key); // s_next.events
                //Expr sNextEvents = DashHelper.sNextEvents(key); // s_next.events
                Expr sNextEvents = DashHelper.eventsPrimed(key);
                Expr sEnvAndIntEvn = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, intEvent); //s.events & InternalEvent
                Expr sNextEnvAndIntEvn = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, intEvent); //s_next.events & InternalEvent
                //s_nextevents & InternalEvent = sendEvent
                Expr ifLowerIf = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, sendExprCom);
            	sPrimeEnvAndIntEvnEqualsEvn = (sPrimeEnvAndIntEvnEqualsEvn == null) ? ifLowerIf : DashHelper.createBinaryExpr(sPrimeEnvAndIntEvnEqualsEvn, ExprBinary.Op.AND ,ifLowerIf);
            	//sendEvent (or none) & (s.events & InternalEvent)
                Expr ifLowerElse = DashHelper.createBinaryExpr(sendExprCom, ExprBinary.Op.PLUS, sEnvAndIntEvn);
                ifLowerElse = (transition.sendExpr == null) ? sEnvAndIntEvn : ifLowerElse;
            	//s_next.events & InternalEvent = sendEvent (or none) + (s.events & InternalEvent)
                Expr sNextIntEqualSendAndInt = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, ifLowerElse);
                sPrimeEvnIntEvnEqualsSend = (sPrimeEvnIntEvnEqualsSend == null) ? sNextIntEqualSendAndInt : DashHelper.createBinaryExpr(sPrimeEvnIntEvnEqualsSend, ExprBinary.Op.AND ,sNextIntEqualSendAndInt);;           

                //s_next.events & InternalEvent = {sendEvent}  
                Expr elseLowerExprIf = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, sendExprCom); //ExprBinary.Op.EQUALS.make(null, null, sNextEnvAndIntEvn, sendExprCom);
                Expr envEvent = DashHelper.envEvent();
                envEvent = DashHelper.addIdentifiersArrow(envEvent, key); // Identifier -> Environment Event
                Expr sPrimeEvtAndEnv = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, envEvent); //s_next.events & EnvironmentEvent
                Expr sEventAndEnv = ExprBinary.Op.INTERSECT.make(null, null, sEvents, envEvent); //s.events & EnvironmentEvent
                elseLowerExprIf = ExprBinary.Op.AND.make(null, null, elseLowerExprIf, ExprBinary.Op.EQUALS.make(null, null, sPrimeEvtAndEnv, sEventAndEnv));
                sNextEvnEqlSEnv = (sNextEvnEqlSEnv == null) ? elseLowerExprIf : DashHelper.createBinaryExpr(sNextEvnEqlSEnv, ExprBinary.Op.AND, elseLowerExprIf);

                Expr elseLowerElse = null;
                Expr sEventsPlusSend = ExprBinary.Op.PLUS.make(null, null, sEvents, sendExprCom);
                elseLowerElse = ExprBinary.Op.EQUALS.make(null, null, sNextEvents, sEventsPlusSend); //s_next.events = s.events + none
                elseLowerElse = (transition.sendExpr == null) ? ExprBinary.Op.EQUALS.make(null, null, sNextEvents, sEvents) : ExprBinary.Op.EQUALS.make(null, null, sNextEvents, sEventsPlusSend); 
                sEnvEqEnvPlusSend = (sEnvEqEnvPlusSend == null) ? elseLowerElse : DashHelper.createBinaryExpr(sEnvEqEnvPlusSend, ExprBinary.Op.AND, elseLowerElse);
            }
            ifLowerExpr = ExprITE.make(null, sStableTrue, sPrimeEnvAndIntEvnEqualsEvn, sPrimeEvnIntEvnEqualsSend);
            ifLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableTrue, ifLowerExpr);          
            elseLowerExpr = ExprITE.make(null, sStableTrue, sNextEvnEqlSEnv, sEnvEqEnvPlusSend);
            elseLowerExpr = ExprBinary.Op.AND.make(null, null, sPrimeStableFalse, elseLowerExpr);
         
            /* Conjunction of any env variables in the model 
             * s_next.envVar = s.envVar
             */
            for(String concStateName: module.envVariableNames.keySet()) {
            	for(String envVar: module.envVariableNames.get(concStateName)) {
            		Expr leftJoin = DashHelper.varPrimed(concStateName + "_" + envVar);
            		Expr rightJoin = DashHelper.createExprVar(concStateName + "_" + envVar);
            		Expr equals = ExprBinary.Op.EQUALS.make(null, null, leftJoin, rightJoin);
            		elseLowerExpr = ExprBinary.Op.AND.make(null, null, elseLowerExpr, equals);
            	}
            }
            
            int iesInOnEvent = 0, iesInSendEvent = 0;
            if (transition.onExpr != null && transition.onExpr.getRawName() != null) {
            	iesInOnEvent = transition.onExpr.getParentConcState().getIdentifiers().size();
            }
            if (transition.sendExpr != null && transition.sendExpr.getRawName() != null) {
            	iesInSendEvent = transition.sendExpr.getParentConcState().getIdentifiers().size();
            }
            
            Expr tFuncCall = ExprVar.make(null, "testIfNextStable" + iesInSendEvent); //s.testIfNextStable
            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, transition.getFullyQualName()), tFuncCall); //tranName.enabledAfterStep_transName
            sendExprCom = (sendExpr == null) ? DashHelper.createExprVar("none") : sendExpr;
            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, sendExprCom, sPrimeGenEventT); // sendEventName.tranName.enabledAfterStep_transName
            expression = ExprBinary.Op.AND.make(null, null, expression, ExprITE.make(null, ssPrimeGenEventT, ifLowerExpr, elseLowerExpr));
            
            if (!eventSize2Trans.containsKey(iesInOnEvent)) {
            	eventSize2Trans.put(iesInOnEvent, new ArrayList<DashTrans>());
            	eventSize2Trans.get(iesInOnEvent).add(transition);
            }
            else {
            	eventSize2Trans.get(iesInOnEvent).add(transition);
            }  
        }
        
        /* Creating the following expression: no (s_next.events & InternalEvent) */
        Expr sendCommandExpr = null;
        if (transition.sendExpr == null && module.isEnvEventModel && !module.stateHierarchy) {
            for (int key: module.eventTuples) { 
            	Expr sNextEvents =  DashHelper.eventsPrimed(key);
            	Expr sNextEnvAndIntEvn = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, DashHelper.intEvent()); //s_next.events & InternalEvent
	        	Expr noEvents = DashHelper.createUnaryExpr(ExprUnary.Op.NO, sNextEnvAndIntEvn);
	            sendCommandExpr = (sendCommandExpr == null) ? noEvents : DashHelper.createExprBadJoin(sendCommandExpr, noEvents); // no (s_next.events & InternalEvent)
            }
        }
        /* Creating the following expression: sentEvent in s_next.events */
        if (transition.sendExpr != null && transition.sendExpr.getRawName() != null) {
        	int i = transition.sendExpr.getParentConcState().getIdentifiers().size();
        	Expr sNextEvents = DashHelper.eventsPrimed(i);
        	sendCommandExpr = ExprBinary.Op.IN.make(null, null, sendExpr, sNextEvents); // sentEvent in s_next.events
        }

        if (sendCommandExpr != null)
            expression = ExprBinary.Op.AND.make(null, null, expression, sendCommandExpr);
        
        /* For managing Enter/Exit commands */        
        DashState destinationState = getState(transition.gotoExpr.gotoExpr.get(0).replace('/', '_'), module);
        if(transition.gotoExpr.gotoExpr.size() > 0 && destinationState != null) {        	
        	Expr gotoExpr = ExprVar.make(null, transition.gotoExpr.gotoExpr.get(0).replace('/', '_'));
        	Expr enterCall = ExprVar.make(null, "enter_" + gotoExpr.toString());
        	
        	if(destinationState.getEnters().size() > 0) {
        		expression = ExprBinary.Op.AND.make(null, null, expression, enterCall);
        	}
        } 
        
        DashState sourceState = getParentSourceState(transition, module);
        expression = createExitAST(expression, sourceState, transition);        
        expression = ExprUnary.Op.NOOP.make(null, expression);
       
        addTransitioPredicate(module, "pos_" + transition.getFullyQualName(), transition.getParentConcState().getIdentifiers(), expression);
    }
    
    private void clearVarChangeContainers() {
        localBufferChanged.clear();
        changedRefVars.clear();
        changedVars.clear();
        changedLocalVars.clear();
    }
    
    /****************************************** SEMANTICS PREDICATE ***************************************/

    /*
     * This function creates the AST for the Semantics predicate in the Alloy Model
     */
    private void createSemanticsAST(DashTrans transition, DashModule module) {
        Expr expression = null;
        Expr transNameExpr = ExprVar.make(null, (transition.getFullyQualName()));
        int totalIEsSize = transition.getParentConcState().getIdentifiers().size();

        /* Creating the following expression: s_next.taken = currentTrans */
        Expr semanticsExpr = null;
        Expr sNextTaken = DashHelper.takenPrimed(totalIEsSize); //taken'
        Expr sTaken = DashHelper.taken(totalIEsSize); //taken
        if (!module.stateHierarchy) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ExprVar.make(null, transition.getFullyQualName())); //s_next.taken = currentTrans
            expression = semanticsExpr;
        }
              
        List<DashTrans> innerTransitions = new ArrayList<DashTrans>();
        if(!module.stateHierarchy) {
        	if(transition.getParent() instanceof DashState && ((DashState) transition.getParent()).getInnerORStates().size() > 0){
        		for(DashState state: ((DashState) transition.getParent()).getInnerORStates())
        			getInnerTransitions(state, innerTransitions);	
        	}
        	
        	for(DashTrans trans: innerTransitions) 
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprVar.make(null, "pre_" + trans.getFullyQualName())));	
        }
        
        /*
         * Creating the following expression: s.stable = True => (s_next.taken + transName)
         * else {...} )
         */
        Expr ifElseExpr = null;
        if (module.stateHierarchy) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, DashHelper.stable(), ExprVar.make(null, "True")); //s.stable = True
            Expr ifRight = transNameExpr; // transName
            for (int i = totalIEsSize - 1; i >= 0; i--) {
            	ifRight = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), ifRight);
            }
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ifRight); //s_next.taken = currentTrans
            Expr noTaken = noTakenSemanticsConstraints("taken", totalIEsSize, module);
            ifExpr = (noTaken == null) ? ifExpr : DashHelper.createBinaryExpr(ifExpr, ExprBinary.Op.AND, noTaken); //no s_next.taken1 and no s_next.taken2
            
            Expr ElseExprLeft = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ExprBinary.Op.PLUS.make(null, null, sTaken, ifRight)); // s_next.taken0 = s.taken0 + transName or s_next.taken = s.taken + (p0 -> p1 -> currentTrans)
            Expr takenEquals = constraintEquals("taken", totalIEsSize, module);
            ElseExprLeft = (takenEquals == null) ? ElseExprLeft : DashHelper.createBinaryExpr(ElseExprLeft, ExprBinary.Op.AND, takenEquals); //s_next.taken1 = s.taken1
            
            Expr elseExprRight = null;
            Expr elseRightBinPlus = null;
            DashConcState transParent = getParentConcState(transition.getParent());
            for (DashTrans trans : module.transitions.values()) {
                if (transParent.getIdentifiers().size() == 0 && getParentConcState(trans.getParent()).getFullyQualName().equals(transParent.getFullyQualName())) {
                	String transitionName = trans.getFullyQualName();
                    if (elseRightBinPlus == null)
                    	elseRightBinPlus = ExprVar.make(null, transitionName);
                    else
                    	elseRightBinPlus = ExprBinary.Op.PLUS.make(null, null, elseRightBinPlus, ExprVar.make(null, transitionName));
                }
            }
            Expr noPTaken = sTaken;
            for (int i = 0; i < totalIEsSize ; i++) {
            	noPTaken = ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p" + i), noPTaken);
            }  
            
            if (elseRightBinPlus != null) {
            	Expr sTaken0 = DashHelper.taken(0);
	            elseExprRight = ExprBinary.Op.INTERSECT.make(null, null, sTaken0, elseRightBinPlus); //no (s.taken & transNames)
	            elseExprRight = ExprUnary.Op.NO.make(null, elseExprRight);
	            ElseExprLeft = DashHelper.createBinaryExpr(ElseExprLeft, ExprBinary.Op.AND, elseExprRight);
            }
            noPTaken = ExprUnary.Op.NO.make(null, noPTaken);
            Expr ElseExpr = transParent.getIdentifiers().size() > 0 ? ExprBinary.Op.AND.make(null, null, ElseExprLeft, noPTaken) : ElseExprLeft;
            ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);                      
            expression = ifElseExpr;
            
        	if(transition.getParent() instanceof DashState && ((DashState) transition.getParent()).getInnerORStates().size() > 0){
        		for(DashState state: ((DashState) transition.getParent()).getInnerORStates())
        			getInnerTransitions(state, innerTransitions);	
        	}
        	
        	for(DashTrans trans: innerTransitions) {
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprVar.make(null, "pre_" + trans.getFullyQualName())));
        	}
        }
        
        expression = ExprUnary.Op.NOOP.make(null, expression);
        
        addTransitioPredicate(module, "semantics_" + transition.getFullyQualName(), transition.getParentConcState().getIdentifiers(), expression);
    }
    
    /****************************************** TRANSITION CALL PREDICATE ***************************************/

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    private void createTransCallAST(DashTrans transition, DashModule module) {
        int totalIEsSize = transition.getParentConcState().getIdentifiers().size();
        Expr expression = null;

        /*
         * Creating the following expressions: post_transName[s, s_next],
         * semantics_transName[s, s_next], pre_transName[s]
         */
        Expr preTransCall = DashHelper.createExprVar("pre_" + transition.getFullyQualName()); //s.pre_transName
        preTransCall = DashHelper.addParametersJoin(preTransCall, totalIEsSize);
    
        Expr postTransCall = DashHelper.createExprVar("pos_" + transition.getFullyQualName()); //s.post_transName
    	postTransCall = DashHelper.addParametersJoin(postTransCall, totalIEsSize); //p.s.pre_transName (For Parameterized Concurrent States)
    	
        expression = DashHelper.createBinaryExpr(preTransCall, ExprBinary.Op.AND, postTransCall); //AND[postTransCall, semanticsCall]

        Expr sematicsCall =  DashHelper.createExprVar("semantics_" + transition.getFullyQualName()); //s.sematics_transName
    	sematicsCall = DashHelper.addParametersJoin(sematicsCall, totalIEsSize); //p.s.pre_transName (For Parameterized Concurrent States)
    	
        expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sematicsCall); //AND[postTransCall, semanticsCall, preTransCall]
        
        // (For Parameterized Concurrent States)
        addTransitioPredicate(module, transition.getFullyQualName(), transition.getParentConcState().getIdentifiers(), expression);
    }
    
    /****************************************** ENABLED AFTER STEP PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    private void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.stateHierarchy) {
            expr = getPreCondForEnabled(transition, module); //Store all the pre-conditions
            int totalIEsSize = transition.getParentConcState().getIdentifiers().size();
            DashConcState transitionParent = getParentConcState(transition.getParent());
            Expr _sStable = DashHelper.stable();
            Expr ifCond = DashHelper.createBinaryExpr(_sStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr()); //_s.stable = True; 

            Expr ifExprLeft = ExprVar.make(null, "t");
            Expr ifExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (transitionParent.getIdentifiers().size() == 0 && getParentConcState(trans.getParent()).getFullyQualName().equals(transitionParent.getFullyQualName())) {
                    if (ifExprRight == null) 
                    	ifExprRight =  ExprVar.make(null, trans.getFullyQualName());
                    else
                    	ifExprRight = ExprBinary.Op.PLUS.make(null, null, ifExprRight, ExprVar.make(null, trans.getFullyQualName()));
                }
            }
            Expr ifExpr = null;
            if (ifExprRight != null) {
            	ifExpr = ExprBinary.Op.INTERSECT.make(null, null, ifExprLeft, ifExprRight); 
            	ifExpr = ExprUnary.Op.NO.make(null, ifExpr);
            }
            
            Expr _sTaken = DashHelper.taken(0);
            Expr elseExprLeft = ExprBinary.Op.PLUS.make(null, null, _sTaken, ExprVar.make(null, "t")); //_s.taken + t
            Expr elseExprRight = null;
            for (DashTrans trans : module.transitions.values()) {
                if (transitionParent.getIdentifiers().size() == 0 && getParentConcState(trans.getParentConcState()).getFullyQualName().equals(transitionParent.getFullyQualName())) {
                    if (elseExprRight == null) 
                        elseExprRight =  ExprVar.make(null, trans.getFullyQualName());
                    else
                        elseExprRight = ExprBinary.Op.PLUS.make(null, null, elseExprRight, ExprVar.make(null, trans.getFullyQualName()));
                }
            }
            Expr elseExpr = null;
            if (elseExprRight != null) {
            	elseExpr = ExprBinary.Op.INTERSECT.make(null, null, elseExprLeft, elseExprRight);
            	elseExpr = ExprUnary.Op.NO.make(null, elseExpr);
            }

            
            Expr noPTaken = DashHelper.takenPrimed(totalIEsSize);
            noPTaken = DashHelper.addParametersJoin(noPTaken, totalIEsSize);
            noPTaken = ExprUnary.Op.NO.make(null, noPTaken);
            if (ifExpr != null && elseExpr != null) {
            	ifExpr = (transitionParent.getIdentifiers().size() > 0) ? DashHelper.createBinaryExpr(ifExpr, ExprBinary.Op.AND, noPTaken) : ifExpr;
            	elseExpr = (transitionParent.getIdentifiers().size() > 0) ? DashHelper.createBinaryExpr(elseExpr, ExprBinary.Op.AND, noPTaken) : elseExpr;
            }
            else {
            	ifExpr = noPTaken;
            	elseExpr = noPTaken;
            }

            String onCommand = transition.onExpr == null ? "" : transition.onExpr.getRawName().replace('/', '_');
            int totalIEsSizeSend = (transition.onExpr == null) ? 0 : transition.onExpr.getParentConcState().getIdentifiers().size();
            if (module.isEnvEventModel && transition.onExpr != null && transition.onExpr.getRawName() != null) {
                Expr _sEvent = DashHelper.events(totalIEsSizeSend);
                Expr envEvent = DashHelper.envEvent();
                envEvent = DashHelper.addParametersArrow(envEvent, totalIEsSizeSend);
                Expr binaryIntersect = DashHelper.createBinaryExpr(_sEvent, ExprBinary.Op.INTERSECT, envEvent);
                Expr binaryPlusIf = DashHelper.createBinaryExpr(binaryIntersect, ExprBinary.Op.PLUS, DashHelper.createExprVar("genEvents")); // (s.events & EnvironmentEvent) + genEvents
                Expr binaryPlusElse = DashHelper.createBinaryExpr(_sEvent, ExprBinary.Op.PLUS, DashHelper.createExprVar("genEvents")); // (s.events + genEvents)
                Expr left = DashHelper.createExprVar(onCommand);
                left = DashHelper.addParametersArrow(left, totalIEsSizeSend);
                Expr binaryInIf = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, binaryPlusIf);
                Expr binaryInElse = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, binaryPlusElse);
                ifExpr = ExprBinary.Op.AND.make(null, null, ifExpr, binaryInIf);
                elseExpr = ExprBinary.Op.AND.make(null, null, elseExpr, binaryInElse);
            }         
            Expr _sStableImpElse = ExprITE.make(null, ifCond, ifExpr, elseExpr);
            expr = ExprBinary.Op.AND.make(null, null, expr, _sStableImpElse);
            
            addEnabledAfterStepPredicate(module, transition, totalIEsSizeSend, expr); 
        }
    }
    
    /****************************************** SMALL STEP PREDICATE ***************************************/
    
    /*
    *  This function creates an AST for the following predicate: pred operation[s,
    *  s_next: Snapshot] { expressions }
    */
    void createSmallStepAST(DashModule module) {
        Expr expression = null;
        for (DashTrans trans : module.transitions.values()) {
        	int iesSize = trans.getParentConcState().getIdentifiers().size();
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            a.add(ExprVar.make(null, "p" + i));
	            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	            a.clear();
            }
            
            Expr expr = ExprVar.make(null, trans.getFullyQualName());
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
            	expr = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), expr);
            }
            expr = (iesSize == 0) ? expr : ExprQt.Op.SOME.make(null, null, decls, expr); // some p: param | transName[s, s_next, p]
            expression = (expression == null) ? expr : ExprBinary.Op.OR.make(null, null, expression, expr);
        }
        
        Expr isEnabled = DashHelper.createExprVar("isEnabled");
        
        Expr equalsCall = DashHelper.createExprVar("equals");
        
        expression = (DashOptions.createLoop) ? DashHelper.createImplesElseExpr(isEnabled, expression, equalsCall) : expression;
       
        module.addFunc(null, null, "small_step", null, null, null, expression);
    }
    
    /****************************************** TEST IF STABLE PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * testIfNextStable[s, s_next: Snapshot, genEvents: set InternalEvent,
     * t:TransitionLabel] {}
     */
    private void createTestIfStableAST(DashModule module) {
        for (int key : eventSize2Trans.keySet()) {
        	Expr expr = null;
        	for (DashTrans trans: eventSize2Trans.get(key)) {
	            List<Decl> decls = new ArrayList<Decl>();
	            List<ExprVar> a = new ArrayList<ExprVar>();
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	                a.add(ExprVar.make(null, "p" + i));
	                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	                a.clear();
	            }
	            
	           	Expr tFuncCall = DashHelper.createExprVar("enabledAfterStep_" + trans.getFullyQualName()); //t.enabledAfterStep_transName
	            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), tFuncCall);
	            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), ssPrimeGenEventT);
	            }
	            
	            Expr quant = (trans.getParentConcState().getIdentifiers().size() == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.NOT, ssPrimeGenEventT) : ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventT);
	            expr = (expr == null) ? quant : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, quant) ; // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
        	}
        	expr = addOtherTestIfState(key, expr);
            expr = ExprUnary.Op.NOOP.make(null, expr); 
            addTestIfStablePredicate(module, "testIfNextStable" + key, key, expr);
    	}
        
        /* For models without any events */
        if (eventSize2Trans.size() == 0) {
        	Expr expr = null;
        	for (DashTrans trans: module.transitions.values()) {
	            List<Decl> decls = new ArrayList<Decl>();
	            List<ExprVar> a = new ArrayList<ExprVar>();
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	                a.add(ExprVar.make(null, "p" + i));
	                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	                a.clear();
	            }
	            
	           	Expr tFuncCall = DashHelper.createExprVar("enabledAfterStep_" + trans.getFullyQualName()); //t.enabledAfterStep_transName
	            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), tFuncCall);
	            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), ssPrimeGenEventT);
	            }
	            
	            Expr quant = (trans.getParentConcState().getIdentifiers().size() == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.NOT, ssPrimeGenEventT) : ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventT);
	            expr = (expr == null) ? quant : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, quant) ; // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
        	}
            expr = ExprUnary.Op.NOOP.make(null, expr); 
            addTestIfStablePredicate(module, "testIfNextStable", 0, expr);
        }
        eventSize2Trans.clear();
    }
    
    private Expr addOtherTestIfState(int key, Expr expr) {
    	Expr expression = expr;
        for (int otherKey : eventSize2Trans.keySet()) { 
        	if (otherKey == key) continue;
        	for (DashTrans trans: eventSize2Trans.get(otherKey)) {
	            List<Decl> decls = new ArrayList<Decl>();
	            List<ExprVar> a = new ArrayList<ExprVar>();
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	                a.add(ExprVar.make(null, "p" + i));
	                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	                a.clear();
	            }
	            
	           	Expr tFuncCall = DashHelper.createExprVar("enabledAfterStep_" + trans.getFullyQualName()); //t.enabledAfterStep_transName
	            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), tFuncCall);
	            Expr none2None = DashHelper.addIdentifiersNone(DashHelper.createExprVar("none"), otherKey);
	            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, none2None, sPrimeGenEventT);
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), ssPrimeGenEventT);
	            }
	            
	            Expr quant = (trans.getParentConcState().getIdentifiers().size() == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.NOT, ssPrimeGenEventT) : ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventT);
	            expression = (expression == null) ? quant : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, quant) ; // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
        	}
        }
        return expression;
    }

    /****************************************** IS ENABLED PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred isEnabled[s:
     * Snapshot] {}
     */
    void createIsEnabledAST(DashModule module) {
        Expr expr = null;
        for (DashTrans trans : module.transitions.values()) {
            int totalIEsSize = trans.getParentConcState().getIdentifiers().size(); 
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            a.add(ExprVar.make(null, "p" + i));
	            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	            a.clear();
            }
            Expr preTransCall = DashHelper.createExprVar("pre_" + trans.getFullyQualName()); //s.pre_transName
            preTransCall = DashHelper.addParametersJoin(preTransCall, totalIEsSize);
            preTransCall = (totalIEsSize == 0) ? preTransCall : ExprQt.Op.SOME.make(null, null, decls, preTransCall); // some p: param | transName[s, s_next, p]
            expr = (expr == null) ? preTransCall : DashHelper.createBinaryExpr(expr, ExprBinary.Op.OR, preTransCall);
        }

        //No need to add this predicate if there are no transitions in the model
        if (module.transitions.keySet().size() > 0 && module.stateHierarchy) {
            module.addFunc(null, null, "isEnabled", null, null, null, expr);
        }
    }
    /****************************************** EQUALS PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred equals[s, s_next:
     * Snapshot] {}
     */
    private void createEqualsAST(DashModule module) {
        Expr expr = null;
        
        for (int i: module.confTuples) {
        	Expr sNextConf = DashHelper.confPrimed(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextConf, ExprBinary.Op.EQUALS, DashHelper.conf(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        for (int i: module.confTuples) {
        	Expr sNextTaken = DashHelper.takenPrimed(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextTaken, ExprBinary.Op.EQUALS, DashHelper.taken(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        for (int i: module.eventTuples) {
        	Expr sNextEvents = DashHelper.eventsPrimed(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.EQUALS, DashHelper.events(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        Expr sNextStable =  DashHelper.stablePrimed();
        Expr stableEquals = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.stable());
        expr = DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, stableEquals);
        
        /* Conjunction of any env variables in the model */
        for(String concStateName: module.envVariableNames.keySet()) {
        	for(String envVar: module.envVariableNames.get(concStateName)) {
        		Expr fullyQualName = DashHelper.createExprVar(concStateName + "_" + envVar);
        		Expr sNextVar = DashHelper.varPrimed(fullyQualName);
        		Expr equals = ExprBinary.Op.EQUALS.make(null, null, sNextVar, fullyQualName);
        		expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        	}
        }

        for (String key : module.variableNames.keySet()) {
            for (String var : module.variableNames.get(key)) {
            	Expr fullyQualVarName = DashHelper.createExprVar(key + "_" + var);
            	Expr sNextVar = DashHelper.varPrimed(fullyQualVarName);
            	Expr equals = DashHelper.createBinaryExpr(sNextVar, ExprBinary.Op.EQUALS, (fullyQualVarName));
            	expr = DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
            }
        }       

        expr = ExprUnary.Op.NOOP.make(null, expr);
        module.addFunc(null, null, "equals", null, null, null, expr);
    }

    /****************************************** INIT PREDICATE ***************************************/
    
    /* This function creates the AST for the init conditions */
    private void createInitAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Map <Integer, ArrayList<Expr>> confToStates = new LinkedHashMap<Integer, ArrayList<Expr>>();
        ExprVar p = ExprVar.make(null, "p");
        a.add(p);

        Expr expression = null;
        isCreatingInit = true;


        for (int key: module.initialDefaultStates.keySet()) {
        	for (DashState state: module.initialDefaultStates.get(key)) {
        		DashConcState parent = getParentConcState(state);
	    		if (!confToStates.containsKey(key)) {
	    			confToStates.put(key, new ArrayList<Expr>());
	    			confToStates.get(key).add(DashHelper.createParameterizedExpr(state.getFullyQualName(), parent));
	    		}
	    		else {
	    			confToStates.get(key).add(DashHelper.createParameterizedExpr(state.getFullyQualName(), parent));
	    		}
        	}
        }

        for (int key: confToStates.keySet()) {
        	Expr sConf = DashHelper.conf(key);
        	Expr right = null;
        	for (Expr expr: confToStates.get(key)) {
        		right = (right == null) ? expr : DashHelper.createBinaryExpr(right, ExprBinary.Op.PLUS, expr);
        	}
    		sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.EQUALS, right);
    		expression = (expression == null) ? sConf : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sConf);
        }
        
        for (int key: confToStates.keySet()) {
        	Expr noSTaken = DashHelper.createUnaryExpr(ExprUnary.Op.NO, DashHelper.taken(key));
    		expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, noSTaken);
        }
        
        if (module.isEnvEventModel) {
            for (int key: module.eventTuples) {
                Expr binary = DashHelper.createBinaryExpr(DashHelper.events(key), ExprBinary.Op.INTERSECT, DashHelper.addIdentifiersArrow(DashHelper.intEvent(), key)); // s.events & InternalEvents
                Expr unary = ExprUnary.Op.NO.make(null, binary); //no s.events & InternalEvent
                expression = ExprBinary.Op.AND.make(null, null, expression, unary);
            }
        }
        
        if(module.stateHierarchy) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, DashHelper.stable(), ExprVar.make(null, "True")); //s.stable = True
        	expression = ExprBinary.Op.AND.make(null, null, expression, sStableTrue);
        }
 
        for (DashInit init : module.initConditions) {
            for (Expr expr : init.exprList) {
                Expr modifiedExpr = getVarFromParentExpr(expr, init.parent, module);
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            }
        }
        
        a.clear();
        decls.clear();
        for (int i = 0; i < module.identifiers.size(); i++) {
        	a.add((ExprVar) DashHelper.createExprVar("p" + i));
            decls.add(new Decl(null, null, null, null, a, DashHelper.createExprVar(module.identifiers.get(i)))); //[p0: IE0]
            a.clear();
        }
        isCreatingInit = false;
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "init", null, decls, null, expression);
    }

    /************************************ HELPER FUNCTION FOR CREATING PREDICATES *****************************************/
    
    /* Add a new Transition predicate to the Dash Module */
    private void addTransitioPredicate(DashModule module, String predName, List<String> ies, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        
        for (int i = 0; i < ies.size(); i++) {
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "p" + i))), ExprVar.make(null, ies.get(i)))); 
        }
        
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /* Add a new IsEnabledAfterStep predicate to the Dash Module */
    private void addEnabledAfterStepPredicate(DashModule module, DashTrans transition, int eventIes, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        
        decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "t"))), ExprVar.make(null, "TransitionLabel")));
        decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "genEvents"))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
        
        for (int i = 0; i < transition.getParentConcState().getIdentifiers().size(); i++) {
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "p" + i))), ExprVar.make(null, transition.getParentConcState().getIdentifiers().get(i)))); 
        }
        
        module.addFunc(null, null, "enabledAfterStep_" + transition.getFullyQualName(), null, decls, null, expression);
    }
    
    private void addTestIfStablePredicate(DashModule module, String name, int eventIes, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        
        decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "t"))), ExprVar.make(null, "TransitionLabel")));
        decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "genEvents"))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
              
        module.addFunc(null, null, name, null, decls, null, expression);
    }
    
    void addSmallStepPredicateAST(DashModule module, String predName, String arg1, String arg2, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        if (arg1 != null)
            a.add(ExprVar.make(null, arg1));
        if (arg2 != null && !DashOptions.isElectrum)
            a.add(ExprVar.make(null, arg2));
        
        decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /****************************************** BIG STEP FACT ***************************************/

    void createBigStepFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s_next");
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr sStable = ExprBinary.Op.JOIN.make(null, null, s, ExprVar.make(null, "stable"));
        
        /*
         * Creating the following expression: (all s: Snapshot | !stable[s] => (one s_next: Snapshot | small_step[s, s_next]))
         */
        Expr notsStable = ExprUnary.Op.NOT.make(null, sStable); //!stable[s]
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s_next.small_step
        smallStepCall = ExprBadJoin.make(null, null, sPrime, smallStepCall); //s.s_next.small_step
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s_next: Snapshot
        Expr qtExpr = ExprQt.Op.ONE.make(null, null, decls, smallStepCall);// one s_next: Snapshot | small_step[s, s_next]
        Expr imples = ExprBinary.Op.IMPLIES.make(null, null, notsStable, qtExpr); // !stable[s] => (one s_next: Snapshot | small_step[s, s_next])
        a.clear();
        decls.clear();
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); // s: Snapshot
        Expr expression = ExprQt.Op.ALL.make(null, null, decls, imples); // all s:Snapshot | !stable[s] => (one s_next: Snapshot | small_step[s, s_next])
        
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFact(null, "completeBigStep", expression);
    }
    
    /****************************************** TRACES FACT ***************************************/
    
    void createElectrumTracesFact(DashModule module) {
    	Expr expression = createInitCall(module, true); // init[first]

    	Expr smallStep = DashHelper.createExprVar("small_step"); //small_step[s]
    	Expr alwaysSmallStep = DashHelper.createUnaryExpr(ExprUnary.Op.ALWAYS, smallStep);
    	
    	expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, alwaysSmallStep);
  
        module.addFact(null, "traces", expression);
    }
    
    Expr createInitCall(DashModule module, boolean isTraces) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        for (int i = 0; i < module.identifiers.size(); i++) {
        	a.add(ExprVar.make(null, "p" + i));
        	decls.add(new Decl(null, null, null, null, a, ExprVar.make(null, module.identifiers.get(i)))); //p0: PID...
        	a.clear();
        }
        
        Expr initCall =  DashHelper.createExprVar("init");
        initCall = DashHelper.addParametersJoin(initCall, module.identifiers.size());
        initCall = ExprQt.Op.ALL.make(null, null, decls, initCall);
        
    	return initCall;
    }
    
    
    /*************************************** KEEPING VARIABLES UNCHANGED ***************************************/
  
    //Find the variables that are unchanged during a transition
    Map<String, DashConcState> getUnchangedVars(List<Expr> exprList, DashModule module) {
    	Map<String, DashConcState> unchangedVariables = new LinkedHashMap<String, DashConcState>(module.variable2ConcState);
      
        for (String var: changedVars.keySet()) {
        	if (unchangedVariables.keySet().contains(var))
        		unchangedVariables.remove(var);
        }
        
        return unchangedVariables;
    }
    
    /*
     * If a parameterized process has constrained its variable using Binary Equals, we need to ensure that the other processes do not
     * change that variable. Assuming that process p has changed its var, we write all quant: param | !(p in quant) => quant.s_next.var = quant.s.var 
     */
    private Expr constrainLocallyChangedVars (String var, DashConcState varParent) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        for (int i = 0; i < varParent.getIdentifiers().size() ; i++) {
        	Expr param = ExprVar.make(null, varParent.getIdentifiers().get(i));
        	param = ExprBinary.Op.MINUS.make(null, null, param, ExprVar.make(null, "p" + i));
            a.add(ExprVar.make(null, "ie" + i));
            decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
            a.clear();
        }    
        
        //Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); 
        Expr binaryLeft = DashHelper.varPrimed(var);
        for (int i = 0; i < varParent.getIdentifiers().size(); i++) {
        	binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryLeft); 
        }
        Expr binaryRight = DashHelper.createExprVar(var); //quant.(s_next).var
        for (int i = 0; i < varParent.getIdentifiers().size(); i++) {
        	binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryRight); 
        }
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        
        return (varParent.getIdentifiers().size() == 0) ? binaryEquals : ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
    }
    
    /*
     * This functions creates the AST for variables that are unchanged during a transition. 
     * If a varibale belongs to a parameterized Conc State, we create the following:
     * p.s_next.var = p'.s_next.var
     * If a varibale belongs to a parameterized Conc State and is not a varibale in the Conc State taking the transition, we create the following:
     * all p: param | p.s_next.var = p.s.var
     */
    private Expr createUnchangedVariableAST(String var, DashConcState varConcState, DashConcState transConcState) {
        //Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); //s_next.variableParent_varName
    	Expr binaryLeft = DashHelper.varPrimed(var);
        Expr binaryRight = DashHelper.createExprVar(var); //s_next.variableParent_varName
        Expr binaryEquals = DashHelper.createBinaryExpr(binaryLeft, ExprBinary.Op.EQUALS, binaryRight);

    	return binaryEquals;
    }
    
    /****************************** Retrieving Variables in Expressions *****************************/
    
    private Expr getVarFromParentExpr(Object parentExpr, DashConcState parent, DashModule module) {    	
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            return getVarFromBinary(exprBinary, parent, module);
        }

        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            return getVarFromUnary(unary, parent, module, false);
        }
        
        if (parentExpr instanceof ExprBadJoin) {
        	return getVarFromBadJoin((ExprBadJoin) parentExpr, parent, module);
        }

        if (parentExpr instanceof ExprQt) {
            return getVarFromExprQt((ExprQt) parentExpr, parent, module, new ArrayList<Decl>(), false);
        }

        if (parentExpr instanceof ExprVar) {
        	return modifyExprWithVar((ExprVar) parentExpr, parent, module, false);
        }
        
        if (parentExpr instanceof ExprList) {
        	return getVarFromExprList((ExprList) parentExpr, parent, module, false);
        }
        
        if (parentExpr instanceof ExprConstant) {
        	return (Expr) parentExpr;
        }
        
        return null;
    }

    /*
     * Breakdown a binary expression into its subcomponents Example of a binary
     * expression: #varible1 = #variable2
     */
    private Expr getVarFromBinary(ExprBinary binary, DashConcState parent, DashModule module) {
    	Expr left = null, right = null;
        if (binary.left instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.left;
            left = getVarFromUnary(unary, parent, module, false);
        }
        if (binary.left instanceof ExprVar) {
            left = modifyExprWithVar(binary.left, parent, module, false);
        }
        if (binary.left instanceof ExprBinary) {
            left = getVarFromBinary((ExprBinary) binary.left, parent, module);
        }
        if (binary.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) binary.left, parent, module);
        }       
        if (binary.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) binary.left, parent, module, false);
        }
        if (binary.left instanceof ExprConstant) {
        	left = binary.left;
        }
        if (binary.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) binary.left, parent, module, false);
        }
        if (binary.left instanceof ExprQt) {
        	left = getVarFromExprQt((ExprQt) binary.left, parent, module, new ArrayList<Decl>(), false);
        }

        if (binary.right instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) binary.right;
            right = getVarFromUnary(unary, parent, module, false);
        }
        if (binary.right instanceof ExprVar) {
            right = modifyExprWithVar(binary.right, parent, module, false);
        }
        if (binary.right instanceof ExprBinary) {
            right = getVarFromBinary((ExprBinary) binary.right, parent, module);
        }
        if (binary.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) binary.right, parent, module);
        }
        if (binary.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) binary.right, parent, module, false);
        }
        if (binary.right instanceof ExprConstant) {
        	right = binary.right;
        }
        if (binary.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) binary.right, parent, module, false);
        }
        if (binary.right instanceof ExprQt) {
        	right = getVarFromExprQt((ExprQt) binary.right, parent, module, new ArrayList<Decl>(), false);
        }
        
        return DashHelper.createBinaryExpr(left, binary.op, right);
    }
    
    private ExprITE getVarFromITE (ExprITE ite, DashConcState parent, DashModule module) {
    	Expr left = null, right = null, cond = null;
        if (ite.left instanceof ExprVar) {
            left = modifyExprWithVar(ite.left, parent, module, false);
        }
        if (ite.left instanceof ExprUnary) {
            left = getVarFromUnary((ExprUnary) ite.left, parent, module, false);
        }
        if (ite.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) ite.left, parent, module);
        }
        if (ite.left instanceof ExprBinary) {
        	left = getVarFromBinary((ExprBinary) ite.left, parent, module);
        }
        if (ite.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) ite.left, parent, module, false);
        }
        if (ite.left instanceof ExprITE) {
        	left = getVarFromITE((ExprITE) ite.left, parent, module);
        }
        if (ite.left instanceof ExprConstant) {
        	left = ite.left;
        }
                
        if (ite.right instanceof ExprVar) {
            right = modifyExprWithVar(ite.right, parent, module, false);
        }
        if (ite.right instanceof ExprUnary) {
            right = getVarFromUnary((ExprUnary) ite.right, parent, module, false);
        }
        if (ite.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) ite.right, parent, module);
        }
        if (ite.right instanceof ExprBinary) {
        	right = getVarFromBinary((ExprBinary) ite.right, parent, module);
        }
        if (ite.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) ite.right, parent, module, false);
        }
        if (ite.right instanceof ExprITE) {
        	right = getVarFromITE((ExprITE) ite.right, parent, module);
        }
        if (ite.right instanceof ExprConstant) {
        	right = ite.right;
        }  
        
        if (ite.cond instanceof ExprVar) {
        	cond = modifyExprWithVar(ite.cond, parent, module, false);
        }
        if (ite.cond instanceof ExprUnary) {
        	cond = getVarFromUnary((ExprUnary) ite.cond, parent, module, false);
        }
        if (ite.cond instanceof ExprBadJoin) {
        	cond = getVarFromBadJoin((ExprBadJoin) ite.cond, parent, module);
        }
        if (ite.cond instanceof ExprBinary) {
        	cond = getVarFromBinary((ExprBinary) ite.cond, parent, module);
        }
        if (ite.cond instanceof ExprList) {
        	cond = getVarFromExprList((ExprList) ite.cond, parent, module, false);
        }
        if (ite.cond instanceof ExprITE) {
        	cond = getVarFromITE((ExprITE) ite.cond, parent, module);
        }
        if (ite.cond instanceof ExprConstant) {
        	cond = ite.cond;
        } 
        if (ite.cond instanceof ExprQt) {
        	cond = getVarFromExprQt((ExprQt) ite.cond, parent, module, new ArrayList<Decl>(), false);
        }
        
        return (ExprITE) ExprITE.make(null, cond, left, right);
    }
    
    /*
     * Breakdown a unary expression into its subcomponents Example of an unary
     * expression: one varible
     */
    private ExprUnary getVarFromUnary(ExprUnary unary, DashConcState parent, DashModule module, boolean inNestedQuant) {
    	Expr sub = null;
        if (unary.sub instanceof ExprVar) {
            sub = modifyExprWithVar(unary.sub, parent, module, false);
        }
        if (unary.sub instanceof ExprUnary) {
            sub = getVarFromUnary((ExprUnary) unary.sub, parent, module, inNestedQuant);
        }
        if (unary.sub instanceof ExprBadJoin) {
            sub = getVarFromBadJoin((ExprBadJoin) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprBinary) {
            sub = getVarFromBinary((ExprBinary) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprList) {
        	sub = getVarFromExprList((ExprList) unary.sub, parent, module, inNestedQuant);
        }
        if (unary.sub instanceof ExprQt) {
        	sub = getVarFromExprQt((ExprQt) unary.sub, parent, module, new ArrayList<Decl>(), inNestedQuant);
        }
        if (unary.sub instanceof ExprITE) {
        	sub = getVarFromITE((ExprITE) unary.sub, parent, module);
        }
        if (unary.sub instanceof ExprConstant) {
        	sub = unary.sub;
        }

        return DashHelper.createUnaryExpr(unary.op, sub);
    }

    /*
     * Breakdown a Join expression into its subcomponents Example of a join
     * expression: s.variable (jointed by a dot)
     */
    private ExprBadJoin getVarFromBadJoin(ExprBadJoin joinExpr, DashConcState parent, DashModule module) {
    	Expr left = null, right = null;
        if (joinExpr.left instanceof ExprVar) {
            left = modifyExprWithVar(joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprUnary) {
            left = getVarFromUnary((ExprUnary) joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprBadJoin) {
            left = getVarFromBadJoin((ExprBadJoin) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprBinary) {
        	left = getVarFromBinary((ExprBinary) joinExpr.left, parent, module);
        }
        if (joinExpr.left instanceof ExprList) {
        	left = getVarFromExprList((ExprList) joinExpr.left, parent, module, false);
        }
        if (joinExpr.left instanceof ExprConstant) {
        	left = joinExpr.left;
        }
                
        if (joinExpr.right instanceof ExprVar) {
            right = modifyExprWithVar(joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprUnary) {
            right = getVarFromUnary((ExprUnary) joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprBadJoin) {
            right = getVarFromBadJoin((ExprBadJoin) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprBinary) {
        	right = getVarFromBinary((ExprBinary) joinExpr.right, parent, module);
        }
        if (joinExpr.right instanceof ExprList) {
        	right = getVarFromExprList((ExprList) joinExpr.right, parent, module, false);
        }
        if (joinExpr.right instanceof ExprConstant) {
        	right = joinExpr.right;
        }  
        
        manageBufferCall(left, right, module, parent);
        
        if (refParamChanged) {
        	refParamChanged = false;
        }

        if (paramBuffer.size() > 0) {
        	right = ExprBadJoin.make(null, null, left, right); //(pid.s.bufferName).add
        	Expr bufferName = DashHelper.createExprVar(paramBuffer.keySet().stream().findFirst().get());
        	Expr sNextJoinBuffer = DashHelper.varPrimed(bufferName); //s_next.bufferName
        	left = ExprBadJoin.make(null, null, paramBuffer.get(paramBuffer.keySet().stream().findFirst().get()), sNextJoinBuffer); //(pid.s_next.bufferName)
            paramBuffer.clear();
        }  
           
        return (ExprBadJoin) ExprBadJoin.make(null, null, left, right);
    }
    
    /*
     * Breakdown a list of expressions into its subcomponents
     */
    private ExprList getVarFromExprList(ExprList list, DashConcState parent, DashModule module, boolean inNestedExprQt) {
    	List<Expr> exprList = new ArrayList<Expr>();
    	for(Expr expr: list.args) {
    		if(expr instanceof ExprQt) {
    			exprList.add(getVarFromExprQt((ExprQt) expr, parent, module, new ArrayList<Decl>(), inNestedExprQt));
    		}
    		if(expr instanceof ExprList) {
    			exprList.add(getVarFromExprList((ExprList) expr, parent, module, inNestedExprQt));
    		}
            if (expr instanceof ExprUnary) {
            	exprList.add(getVarFromUnary((ExprUnary) expr, parent, module, false));
            }
            if (expr instanceof ExprBinary) {
            	exprList.add(getVarFromBinary((ExprBinary) expr, parent, module));
            }
            if (expr instanceof ExprBadJoin) {
            	exprList.add(getVarFromBadJoin((ExprBadJoin) expr, parent, module));
            }
            if (expr instanceof ExprVar) {
            	exprList.add(modifyExprWithVar(expr, parent, module, false));
            }
            if (expr instanceof ExprITE) {
            	exprList.add(getVarFromITE((ExprITE) expr, parent, module));
            }
            if (expr instanceof ExprConstant) {
            	exprList.add(expr);
            }
    	}
    	return DashHelper.createExprList(list.op, exprList);
    }    
    
    /*
     * Breakdown a quantified expression into its subcomponents. An example of a quantified expression is:
     * all p: PID | expression
     */
    private Expr getVarFromExprQt(ExprQt exprQt, DashConcState parent, DashModule module, List<Decl> args, boolean nestedInExprQt) {
    	Expr subExpr = null;
    	List<Decl> decls = new ArrayList<Decl>();
    	List<Decl> arguments = new ArrayList<>(args);
    	isCreatingExprQt = true;
	
        for (Decl decl : exprQt.decls) {
        	List<ExprVar> a = new ArrayList<ExprVar>();
  	
        	for(ExprHasName name: decl.names)
        		a.add(ExprVar.make(null, name.toString()));    
        	Expr b = getVarFromParentExpr(decl.expr, parent, module);       	
        	decls.add(new Decl(null, null, null, null, a, mult(b)));
        }
   
        if (exprQt.sub instanceof ExprQt) {
        	subExpr = getVarFromExprQt((ExprQt) exprQt.sub, parent, module, arguments, true);
        }
        if (exprQt.sub instanceof ExprUnary) {
        	subExpr = getVarFromUnary((ExprUnary) exprQt.sub, parent, module, true);
        }
        if (exprQt.sub instanceof ExprBinary) {
        	subExpr = getVarFromBinary((ExprBinary) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprVar) {
        	subExpr = modifyExprWithVar(exprQt.sub, parent, module, true);
        }
        if(exprQt.sub instanceof ExprList) {
        	subExpr = getVarFromExprList((ExprList) exprQt.sub, parent, module, true);
        }
        if(exprQt.sub instanceof ExprBadJoin) {
        	subExpr = getVarFromBadJoin((ExprBadJoin) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprITE) {
        	subExpr = getVarFromITE((ExprITE) exprQt.sub, parent, module);
        }
        if (exprQt.sub instanceof ExprConstant) {
        	subExpr = exprQt.sub;
        }  

    	isCreatingExprQt = false;
        
        return DashHelper.createExprQt(exprQt.op, decls, subExpr);
    }
    
    
    /*************************************** MODIFY EXPRESSIONS WITH VARS ***************************************/

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game concurrent state)
    private Expr modifyExprWithVar(Expr expr, DashConcState parent, DashModule module, Boolean isRef) {
    	DashConcState concState = parent;
    	
        Expr expression = expr; 
        
        /* If the var refers to a parameterizerd concurrent process, return 'p' as this refers to the current process */
        if(expression.toString().equals("this")) {
        	return isCreatingInit && parent.isParameterized()? ExprVar.make(null, "p" + module.identifiers.indexOf(parent.getReplicatedIdentifier())) : ExprVar.make(null, "p0");
        }
    	
        //If we make a reference to a conc state outside of the current conc state, find it and 
        //modify the value of the expression accordingly
        //System.out.println("Expr: " + expr);
    	if(expr.toString().contains("/")) {
    		//String concStateRef = expr.toString().substring(0, expr.toString().indexOf("/"));
    		DashConcState parentConcState = (parent.getParentConcState() == null) ? parent : parent.getParentConcState();
    		concState = DashHelper.getConcStateReferred(expression, parentConcState);
    		expression = ExprVar.make(null, expr.toString().substring(expr.toString().lastIndexOf("/") + 1));  
    		return modifyExprWithVar(expression, concState, module, true);
    	} 
    	
        final List<String> variablesInParent = module.variableNames.get(concState.getFullyQualName());
        final List<String> envVariablesInParent = module.envVariableNames.get(concState.getFullyQualName());
        
        DashConcState outerConcState = concState.getParentConcState();

        if (variablesInParent != null)
            expression = modifyVar(module, expression, concState, expr, variablesInParent, false, isRef);
        if (envVariablesInParent != null)
            expression = modifyVar(module, expression, concState, expr, envVariablesInParent, true, isRef);
        
        for (DashConcState innerConcState: concState.getInnerConcStates()) {
            if (module.variableNames.get(innerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, innerConcState, expr, module.variableNames.get(innerConcState.getFullyQualName()), false, isRef);
            if (module.envVariableNames.get(innerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, innerConcState, expr, module.envVariableNames.get(innerConcState.getFullyQualName()), true, isRef);
        }

        while (outerConcState != null) {
            if (module.variableNames.get(outerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, outerConcState, expr, module.variableNames.get(outerConcState.getFullyQualName()), false, isRef);
            if (module.envVariableNames.get(outerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, outerConcState, expr, module.envVariableNames.get(outerConcState.getFullyQualName()), true, isRef);
            outerConcState = outerConcState.getParentConcState();
        }
        
        expression = replaceWithActionExpr(expression, concState, module);
        expression = replaceWithConditionExpr(expression, concState, module);
        
        return expression;
    }
        
    private Expr modifyVar(DashModule module, Expr expression, DashConcState parent, Expr expr, List<String> exprList, boolean isEnvVar, boolean isRef) {
        for (String var : exprList) {
        	String qualifiedVarName = parent.getFullyQualName() + '_' + var;
            if (expr.toString().equals(var + "'")) {
            	changedVars.put(qualifiedVarName, parent);
            	if (!isRef) {
            		changedLocalVars.put(qualifiedVarName, parent);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);
            		Expr sNextVar = parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.varPrimed(variable)) : DashHelper.varPrimed(variable);
            		sNextVar = DashHelper.addParametersJoin(sNextVar, parent.getIdentifiers().size());
            		return sNextVar;
            	}
            	else {
            		changedRefVars.add(qualifiedVarName);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);
            		Expr sNextVar = parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.varPrimed(variable)) : DashHelper.varPrimed(variable);
            		return sNextVar;
            	}
            }
            else if (expr.toString().equals(var)) {
            	if (isCreatingEnabledAfterPred && isEnvVar) {
            		return parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.createExprVar(qualifiedVarName)) : DashHelper.createExprVar(qualifiedVarName);
            	}
            	else if (isCreatingEnabledAfterPred && !isRef) {
        			Expr variable = DashHelper.createExprVar(qualifiedVarName);
        			Expr sVarPrimed = parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.varPrimed(variable)) : DashHelper.varPrimed(variable);
        			sVarPrimed = DashHelper.addParametersJoin(sVarPrimed, parent.getIdentifiers().size());
        			return sVarPrimed;
            	}
             	else {
            		if (!isRef && (isCreatingInit) && (!isCreatingExprQt) && parent.getIdentifiers().size() > 0) {
            			Expr variable = parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.createExprVar(qualifiedVarName)) : DashHelper.createExprVar(qualifiedVarName);
            			variable = DashHelper.createBinaryExpr(DashHelper.createExprVar("p" + module.identifiers.indexOf(parent.getReplicatedIdentifier())), ExprBinary.Op.JOIN, variable);
            			//variable = DashHelper.addParametersJoin(variable, parent.getIdentifiers().size());
	                	return variable;
            		}
            		else if (!isRef && !(isCreatingInit && isCreatingExprQt)) { // No need to DotJoin the "p0" expr if it is a reference to another parameterized concurrent state
            			Expr variable = parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.createExprVar(qualifiedVarName)) : DashHelper.createExprVar(qualifiedVarName);
            			variable = DashHelper.addParametersJoin(variable, parent.getIdentifiers().size());
	                	return variable;
                	}
                	else {
                		return parent.getIdentifiers().size() == 0 ? DashHelper.createExprBadJoin("Variables", DashHelper.createExprVar(qualifiedVarName)) : DashHelper.createExprVar(qualifiedVarName);
                	}
            	}
            }
        }
        return expression;
    }
    
    /************************* BUFFER FUNCTIONS **************************/
    
    // A buffer call by the user will look as follows: (s.buffer_name).add or (id.s.buffer_Name). If this is the case: we need to modify this expression as follows:
    //(s_next.buffer_name).(s.buffer_name).add or (id.s_next.buffer_name).(id.s.buffer_name).add.since the call to add is: add[buffer, buffer', p]
    // This gets confusing!
    private void manageBufferCall(Expr left, Expr right, DashModule module, DashConcState parent) {
    	ExprBadJoin joinLeft = null;
        if (left instanceof ExprBadJoin) {
        	 joinLeft = (ExprBadJoin) left;
        	 joinLeft = (ExprBadJoin) breakdownBufferCall(joinLeft, parent);
        	 Expr joinLeftRightRight = null;
        	 if (joinLeft.right instanceof ExprBadJoin) {
        		 joinLeftRightRight = (((ExprBadJoin) joinLeft.right).right == null) ? joinLeft.right : ((ExprBadJoin) joinLeft.right).right;
        	 } else {
        		 joinLeftRightRight = joinLeft.right;
        	 }
        	 //System.out.println("Join Left: " + joinLeft + "  Right: " + right.toString() + " Joinleft.right: " + joinLeftRightRight);
        	 foundBuffer = (bufferCommands.contains(right.toString()) && module.buffers.containsKey(joinLeftRightRight.toString())) ? true : false;
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprVar)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
            	 System.out.println("Join Left: " + joinLeft + " joinLeftRight: " + joinLeftRight);
        		 if (module.buffers.containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing1: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.buffers.get(joinLeftRight.right.toString()));
        			 if (module.buffers.get(joinLeftRight.right.toString()).isParameterized()) {
        				 paramBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: (p.bufferName).remove [a buffer call with no parameters such as remove]
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprVar && joinLeft.left instanceof ExprVar)) {
        		 ExprVar joinLeftRight = (ExprVar) joinLeft.right;
        		 if (module.buffers.containsKey(joinLeftRight.toString()) && bufferCommands.contains(right.toString())) {
        			 System.out.println("ChangingBuffer2: " + joinLeftRight.toString() + " Left: " + joinLeft + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.toString(), module.buffers.get(joinLeftRight.toString()));
        			 if (joinLeft.left.toString().equals("p0"))
        				 changedLocalVars.put(joinLeftRight.toString(), module.buffers.get(joinLeftRight.toString()));
        			 if (module.buffers.get(joinLeftRight.toString()).isParameterized()) {
        				 localBufferChanged.put(joinLeftRight.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: ConcState[buffer1.first]/buffer0.add[pid]
        	 //System.out.println("JoinLeft Right Type: " + joinLeft.right.getClass().getCanonicalName() + " JoineLeft Left Type: " + joinLeft.left.getClass().getCanonicalName());
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprVar && joinLeft.left instanceof ExprBadJoin)) {
        		 ExprVar joinLeftRight = (ExprVar) joinLeft.right;
        		 //System.out.println("joinLeftRight: " + joinLeftRight + " Right: " + right.toString());
        		 if (module.buffers.containsKey(joinLeftRight.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing3: " + joinLeftRight.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.toString(), module.buffers.get(joinLeftRight.toString()));
        			 if (module.buffers.get(joinLeftRight.toString()).isParameterized()) {
        				 localBufferChanged.put(joinLeftRight.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        }
        if (foundBuffer && joinLeft != null) {
        	changedVars.put(joinLeft.right.toString(), parent);
        }
        //System.out.println("Found? " + foundBuffer);
    }
    
    Expr breakdownBufferCall (ExprBadJoin joinLeft, DashConcState parent) {
    	for (int i = 0; i < parent.getIdentifiers().size() - 1; i++) {
    		if (joinLeft.right instanceof ExprBadJoin) {
    			joinLeft = (ExprBadJoin) joinLeft.right;
    		}
    	}
    	return joinLeft;
    }

    /*************************** OPEATIONS AXIOM ******************************/  
    
    void createOperationsAxiomAST(DashModule module)
    {
        //This is the Operations Axiom, some s, s_next : S | T[s, s] for every transition T
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr s = ExprVar.make(null, "s");
        Expr sNext = ExprVar.make(null, "s_next");
        a.add((ExprVar) s);
        a.add((ExprVar) sNext);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s_next: Snapshot
        
        Expr expression = null;
        for (String transName: module.transitions.keySet())
        {
        	Expr sJoinTrans = ExprBadJoin.make(null, null, s, ExprVar.make(null, transName)); //T[s] or s.T
        	Expr join = ExprBadJoin.make(null, null, sNext, sJoinTrans); // T[s, s_next] or s_next.s.T
        	Expr quantified = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), join); // some s, s_next: Snapshot | T[s, s_next]
        	
        	if (expression == null)
        		expression = quantified;
        	else
        		expression = ExprBinary.Op.AND.make(null, null, expression, quantified);
        }
        
        //addPredicateAST(module, "operationsAxiom", null, null, null, null, expression);
    }
    
    /*************************** HELPER FUNCTIONS ******************************/
    /*
     * Convert ExprVar expression to ExprUnary
     */
    private Expr convertToExprUnary(Expr b) {
    	if (b instanceof ExprVar) {
    		return ExprUnary.Op.SETOF.make(null, b);
    	}
    	return b;
    }
    
    /*
     * Taken from the Dash.cup file. It is used for handling difficult parsing
     * ambiguities with Alloy expressions
     */
    private Expr mult(Expr x) throws Err {
        if (x instanceof ExprUnary) {
            ExprUnary y = (ExprUnary) x;
            if (y.op == ExprUnary.Op.SOME)
                return ExprUnary.Op.SOMEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.LONE)
                return ExprUnary.Op.LONEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.ONE)
                return ExprUnary.Op.ONEOF.make(y.pos, y.sub);
        }
        return x;
    }
    
    /* Get all the transitions within a state */
    private void getInnerTransitions(DashState state, List<DashTrans> transitions) {
    	for(DashTrans trans: state.getTransitions()) {
    		transitions.add(trans);
    	}
    	
    	for(DashState innerState: state.getInnerORStates()) {
    		getInnerTransitions(innerState, transitions);
    	}
    }
    
    //Retrive the concurrent state inside which "item" is located
    DashConcState getParentConcState(Object item) {
    	
        if (item instanceof DashState) {
            if (((DashState) item).getParent() instanceof DashState)
                return getParentConcState(((DashState) item).getParent());
            if (((DashState) item).getParent() instanceof DashConcState)
                return (DashConcState) ((DashState) item).getParent();
        }

        if (item instanceof DashConcState)
            return (DashConcState) item;

        return null;
    }
    
    DashState getState(String stateName, DashModule module) {
    	return module.states.get(stateName);
    }
    
    /* Get all the transitions declared within a concurrent state */
    private List<String> getTransitions(DashModule module, DashConcState concState)
    {
    	List<String> transitions = new ArrayList<String>();
    	for (DashTrans trans: module.transitions.values()) {
    		if (getParentConcState(trans.getParent()).getFullyQualName().equals(concState.getFullyQualName()))
    			transitions.add(trans.getFullyQualName());
    	}
    	return transitions;
    }
    
    /* Get all the states declared within a concurrent state */
    private List<DashState> getStates(DashConcState concState)
    {
    	List<DashState> states = new ArrayList<DashState>();
    	for (DashState state: concState.getInnerORStates()) {
    		states.add(state);
    		states.addAll(getInnerStates(state));
    	}
    	return states;
    }
    
    private int getBasicStateCount(List<DashState> states) {
    	int i = 0;
    	for (DashState state: states) {
    		if (state.getInnerORStates().size() == 0) {
    			i++;
    		}
    	}
    	return i;
    } 
    
    private List<DashState> getInnerStates (DashState state)
    {
    	List<DashState> states = new ArrayList<DashState>();
    	for (DashState innerState: state.getInnerORStates()) {
    		states.add(innerState);
    		if (innerState.getInnerORStates().size() > 0) 
    			states.addAll(getInnerStates(innerState));
    	}
    	return states;
    }
    
    /* Get the parent OR state of an OR state (if it is a child state) */
    private DashState getParentSourceState(DashTrans trans, DashModule module) {   	
    	DashState sourceState = getState(trans.getOrigin().fromExpr.get(0), module);
    	
    	if(sourceState == null)
    		return null;
    	
    	/* If a source state is a child of a parent OR state, then we need to transition from that state */
    	while(sourceState.getParent() instanceof DashState) {  		
    		sourceState = (DashState) (sourceState).getParent();
    	}
    	
    	return sourceState;
    }
    
    /*************************** ENTER/EXIT FUNCIONS ******************************/
    
    public void createEnterPredAST(DashModule module) {
    	Expr expr = null;
    	for(DashState state: module.states.values()) {
    		for(DashEnter enter: state.getEnters()) {
    			expr = getVarFromParentExpr(enter.expr, getParentConcState(state.getParent()), module);
    			//addPredicateAST(module, "enter_" + state.getFullyQualName(), "s", null, null, null, expr);
    		}
    	}
    }
    
    public void createExitPredAST(DashModule module) {
    	Expr expr = null;
    	for(DashState state: module.states.values()) {
    		for(DashExit exit: state.getExits()) {
    			expr = getVarFromParentExpr(exit.expr, getParentConcState(state.getParent()), module);
    			//addPredicateAST(module, "exit_" + state.getFullyQualName(), "s", null, null, null, expr);
    		}
    	}
    }
    
    private Expr createExitAST(Expr expression, DashState sourceState, DashTrans transition) {
        if(transition.getOrigin().fromExpr.size() > 0 && sourceState != null) {        	
        	Expr fromExpr = ExprVar.make(null, sourceState.getFullyQualName());
        	Expr sConf = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "conf")); //s.conf
        	Expr in = ExprBinary.Op.IN.make(null, null, fromExpr, sConf); //source in s.conf
        	Expr some = ExprUnary.Op.SOME.make(null, ExprBinary.Op.INTERSECT.make(null, null, fromExpr, sConf)); //source & s.conf
        	Expr exitCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, "exit_" + fromExpr.toString()));
        	
            if(sourceState.getInnerORStates().size() > 0) {
            	for(DashState state: sourceState.getInnerORStates()) {
            		if(state.isDefault())
            			expression = createExitAST( expression,  state, transition);
            	}     		
            }
        	
        	if(sourceState.getExits().size() > 0 && sourceState.getInnerORStates().size() == 0) {
        		return ExprBinary.Op.AND.make(null, null, expression, ExprBinary.Op.IMPLIES.make(null, null, in, exitCall));
        	}
        	else if(sourceState.getExits().size() > 0 && sourceState.getInnerORStates().size() > 0) {
        		return ExprBinary.Op.AND.make(null, null, expression, ExprBinary.Op.IMPLIES.make(null, null, some, exitCall));
        	}
        }
        return expression;
    }
    
    /**************************************** ACTION/CONDITION FUNCTIONS **********************************/
    
    private Expr replaceWithActionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashAction value : module.actions.values()) {
                if (expr.toString().equals(value.name))
                	return getVarFromParentExpr(value.expr, parent, module);
            }
        }
        return expr;
    }
    
    private Expr replaceWithConditionExpr(Expr expr, DashConcState parent, DashModule module) {
        if(expr instanceof ExprVar) {
            for (DashCondition value : parent.getConditions()) {
                if (expr.toString().equals(value.getRawName()))
                	return getVarFromParentExpr(value.getExpr(), parent, module);
            }
        }
        return expr;
    }
    
    /***************************** CREATING INVARIANT FACT *******************************/
    
    private void createInvariantFact(DashModule module) {
    	for(DashInvariant invar: module.invariants.values()) {
    		addInvariantFact(invar, module);
    	}
    }

    private void addInvariantFact(DashInvariant invar, DashModule module) {
    	Expr expression = null;

    	for(Expr expr: invar.exprList) {
    		if (expression == null)
    			expression = getVarFromParentExpr(expr, getParentConcState(invar.parent), module);
    		else
    			expression = ExprBinary.Op.AND.make(null, null, getVarFromParentExpr(expr, getParentConcState(invar.parent), module), expression);
        }

        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(snapshot)));

    	Expr quantifiedExpr = ExprQt.Op.ALL.make(null, null, decls, expression);

    	module.addFact(null, invar.name, quantifiedExpr);
    }
    
    /*************************** COMMAND FUNCIONS ******************************/
    
    private void convertCommand(DashModule module) {
    	for (int i = 0; i < module.commands.size(); i++) {
    		module.commands.set(i, modifyCommand(module.commands.get(i), module));
    	}
    }
    
    public Command modifyCommand(Command command, DashModule module){
    	List<CommandScope> scopes = new ArrayList<CommandScope>();
		int paramScope = 2;
		int totalParamScope = 0;
		int stateLabelScope = 0;
		int transitionLabelScope = 0;
		
    	for (CommandScope scope: command.scope) {
    		if (module.rawBufferNameToIndex.containsKey(scope.sig.label)) {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(module.rawBufferNameToIndex.get(scope.sig.label), AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);
    		}
    		else if (module.bufferParamToConcState.containsKey(scope.sig.label)){
    			paramScope = scope.endingScope;
    			totalParamScope += paramScope;

	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);    			
    		}
    		else {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);  
    		}
    	}
    	
		for (DashConcState concState: module.concStates.values()) {
			stateLabelScope += getBasicStateCount(getStates(concState));
			transitionLabelScope += getTransitions(module, concState).size();
		}
		
		CommandScope stateNumber = new CommandScope(null            , Sig.NONE, true,          stateLabelScope, stateLabelScope,             1    );
		CommandScope stateSigScope = new CommandScope(null, new PrimSig("StateLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), stateNumber.isExact, stateNumber.startingScope, stateNumber.endingScope, stateNumber.increment);
		scopes.add(stateSigScope);
		
		CommandScope transitionNumber = new CommandScope(null            , Sig.NONE, true,          transitionLabelScope, transitionLabelScope,             1    );
		CommandScope transitionSigScope = new CommandScope(null, new PrimSig("TransitionLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), transitionNumber.isExact, transitionNumber.startingScope, transitionNumber.endingScope, transitionNumber.increment);
		scopes.add(transitionSigScope);
        
        int eventLabelScope = 0;
        if(module.isEnvEventModel) {
        	eventLabelScope = module.event2ConcState.size();
        }
        
		CommandScope number = new CommandScope(null            , Sig.NONE, true,          eventLabelScope, eventLabelScope,             1    );
		CommandScope sigScope = new CommandScope(null, new PrimSig("EventLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), number.isExact, number.startingScope, number.endingScope, number.increment);
		scopes.add(sigScope);
		
		CommandScope identNumber = new CommandScope(null            , Sig.NONE, true,          totalParamScope, totalParamScope,             1    );
		CommandScope identifiersScope = new CommandScope(null, new PrimSig("Identifiers", AttrType.WHERE.make(new Pos(null, 0, 0))), identNumber.isExact, identNumber.startingScope, identNumber.endingScope, identNumber.increment);
		scopes.add(identifiersScope);
		
		return command.check ? createCommand(false,ExprVar.make(null, "c"), null , ExprVar.make(null, command.label) ,null, scopes, null, module) : createCommand(false,ExprVar.make(null, "r"), null , ExprVar.make(null, command.label) ,null, scopes, null, module);
    }
    
    
    //Taken from the Dash.cup file for adding in commands
    private Command createCommand(boolean follow, ExprVar o, ExprVar x, ExprVar n, Expr e, List<CommandScope> s, ExprConstant c, DashModule module) throws Err {
        int bitwidth=(-1), maxseq=(-1), overall=(-1), expects=(c==null ? -1 : c.num);
        int maxtime = (-1), mintime = (-1);
        Pos p;
		if(e != null)
        	p = o.pos.merge(n!=null ? n.span() : e.span());
        for(int i=s.size()-1; i>=0; i--) {
          Sig j=s.get(i).sig;  int k=s.get(i).startingScope;
          //p=p.merge(j.pos);
          if (j.label.equals("univ")) { overall=k; s.remove(i); continue; }
          if (j.label.equals("int"))  { if (bitwidth>=0) throw new ErrorSyntax(j.pos, "The bitwidth cannot be specified more than once."); bitwidth=k; s.remove(i); continue; }
          if (j.label.equals("seq"))  { if (maxseq>=0) throw new ErrorSyntax(j.pos, "The maximum sequence length cannot be specified more than once."); maxseq=k; s.remove(i); continue; }
          // [electrum] process time scopes
          if (j.label.equals("stepUtil")) {
              if (s.get(i).endingScope == Integer.MAX_VALUE && s.get(i).startingScope != 1) throw new ErrorSyntax(j.pos, "Unbounded time scope must start at 1.");
	      	  if (s.get(i).increment != 1) throw new ErrorSyntax(j.pos, "Step scopes must be incremented by 1.");
          	  if (k<1) throw new ErrorSyntax(j.pos, "Trace solutions must contain at least one step.");
        	  if (maxtime>=0) throw new ErrorSyntax(j.pos, "Steps scope cannot be specified more than once."); 
        	  maxtime=k; 
        	  if (s.get(i).isExact) mintime = k; 
        	  else if (s.get(i).endingScope != s.get(i).startingScope) { 
        	  	maxtime = s.get(i).endingScope; mintime = s.get(i).startingScope; }
        	  s.remove(i); continue; 
      	  }
        }
        return addCommand(follow, null, n, o.label.equals("c"), overall, bitwidth, maxseq, mintime, maxtime, expects, s, x, module);
    }

	/** Add a COMMAND declaration. */
    public Command addCommand(boolean followUp, Pos pos, ExprVar name, boolean check, int overall, int bitwidth, int seq, int tmn, int tmx, int exp, List<CommandScope> scopes, ExprVar label, DashModule module) throws Err {
        if (followUp && !Version.experimental)
            throw new ErrorSyntax(pos, "Syntax error encountering => symbol.");
        if (label != null)
            pos = Pos.UNKNOWN.merge(pos).merge(label.pos);
        if (name.label.length() == 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot be empty.");
        if (name.label.indexOf('@') >= 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot contain \'@\'");
        String labelName = (label == null || label.label.length() == 0) ? name.label : label.label;
        Command parent = followUp ? module.commands.get(module.commands.size() - 1) : null;
        Command newcommand = new Command(pos, name, labelName, check, overall, bitwidth, seq, tmn, tmx, exp, scopes, null, name, parent);
        return newcommand;
    }
    
	public Expr constraintEquals(String type, int conf, DashModule module) {
		Expr equals = null;
		for (int key: module.confTuples) {
			if (key == conf) {
				continue;
			}
			Expr sRight = DashHelper.createExprVar(type + key); 
			Expr sNextLeft = DashHelper.varPrimed(type + key);
			Expr equal = DashHelper.createBinaryExpr(sNextLeft, ExprBinary.Op.EQUALS, sRight);
			equals = equals == null ? equal : DashHelper.createBinaryExpr(equals, ExprBinary.Op.AND, equal);
		}
		return equals;
	}
	
	public Expr noTakenSemanticsConstraints(String type, int taken, DashModule module) {
		Expr equals = null;
		for (int key: module.confTuples) {
			if (key == taken) {
				continue;
			}
			Expr sNextTaken =  DashHelper.varPrimed(type + key);
			Expr noSNextTaken = DashHelper.createUnaryExpr(ExprUnary.Op.NO, sNextTaken);
			equals = equals == null ? noSNextTaken : DashHelper.createBinaryExpr(equals, ExprBinary.Op.AND, noSNextTaken);
		}
		return equals;
	}
}
