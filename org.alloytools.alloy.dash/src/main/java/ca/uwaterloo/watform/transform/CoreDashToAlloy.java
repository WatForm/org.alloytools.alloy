package ca.uwaterloo.watform.transform;

import java.lang.ref.Reference;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

//Dash Imports
import ca.uwaterloo.watform.ast.*;
import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;

//Alloy Imports
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Attr.*;
import edu.mit.csail.sdg.ast.Sig.*;

public class CoreDashToAlloy {
	boolean isCreatingEnabledAfterPred;
	boolean isCreatingPreCond;
	boolean isCreatingInit;
	boolean isCreatingInvariant;
	boolean isCreatingExprQt;
	 
	Map <Integer, List<DashTrans>> eventSize2Trans;
	Map<String, DashConcState> changedLocalVars; // Variables changed only locally
	List<String> changedRefVars; // Variables changed by reference in the transitions being checked
	Map<String, DashConcState> changedVars; // Keep a track of when a variable has been changed during a transition
	boolean changingVar;
	boolean refParamChanged;

	Map<String, Expr> paramBuffer;
	Map<String, Expr> paramBufferChanged ;
	Map<String, Expr> localBufferChanged ;
	// Buffer Helpers
	List<String> bufferCommands;
	List<String> bufferFuncCommands;
	// Changed parameterized buffers that are universally quantified (No need to keep this unchanged for other replicated processes since it is universally quantified for all elements in a set of Processes
	Map<String, Expr> universalQuantBuffers;
	boolean foundBuffer;
	boolean legalConstraint ;
	
	public CoreDashToAlloy () {
		eventSize2Trans = new LinkedHashMap<Integer, List<DashTrans>>();
		changedLocalVars = new LinkedHashMap<String, DashConcState>();
		changedRefVars = new ArrayList<String>();
		changedVars = new LinkedHashMap<String, DashConcState>();
		paramBuffer = new LinkedHashMap<String, Expr>();
		paramBufferChanged = new LinkedHashMap<String, Expr>();
		localBufferChanged = new LinkedHashMap<String, Expr>();
		bufferCommands = Arrays.asList(new String[]{"addFirst", "add", "remove", "removeFirst"});
		bufferFuncCommands = Arrays.asList(new String[]{"firstElem"});
		universalQuantBuffers = new LinkedHashMap<String, Expr>();
	}

    public DashModule convertToAlloyAST(DashModule module, String fileName, String path) {	
    	DashModule alloyModule = new DashModule(module, fileName, path, true);
    	
    	convertCommand(alloyModule);
    	createrBufIdxSig(alloyModule);
    	createParamSigAST(alloyModule);
        createSnapshotSigAST(alloyModule);

        if (DashOptions.ctlModelChecking) {
        	createReachabilityFact(alloyModule);
        }

        createStateSpaceAST(alloyModule);
        createEventSpaceAST(alloyModule);
        createTransitionSpaceAST(alloyModule);
        
        createStableAST(alloyModule);
        
        createTransitionsAST(alloyModule);
        
        createInitAST(alloyModule);
        if(module.getAllConcurrentStates().size() > 1) {
            createTestIfStableAST(alloyModule);
        }
        createSmallStepAST(alloyModule);
        
        createEqualsAST(alloyModule);
        //if (DashOptions.generateTraces) {
        //	createDifferentAtomsFact(module);
        //}
        //createParamConstFactAST(module);
        if(DashOptions.generateTraces && !DashOptions.isElectrum) {
        	createTracesFact(alloyModule);
        }
        else if (!DashOptions.generateTraces && alloyModule.hasHierarchy() && !DashOptions.isElectrum) {
        	createBigStepFact(alloyModule);
        }
        if (DashOptions.isElectrum) {
        	createElectrumTracesFact(alloyModule);
        }

        createIsEnabledAST(alloyModule);
        if (!DashOptions.isElectrum) {
        	createPathAST(alloyModule);
        }
        if (DashOptions.generateSigAxioms && !DashOptions.isElectrum) {
        	//createSignificanceAxiomAST(module);
        	//createOperationsAxiomAST(module);
        }
        if (DashOptions.ctlModelChecking && !DashOptions.isElectrum) {
        	createCTLFact(alloyModule);
        }
        createInvariantFact(alloyModule);
        
        if (DashOptions.hasEvents && DashOptions.assumeSingleInput) {
        	createSingleStepFact(alloyModule);
        }

        return alloyModule;
    }

    /**************************** CREATING ALL SIGNATURES *****************************/
    
    private void createrBufIdxSig (DashModule module) {
    	for (String bufIdx: module.getBufferIndexSig().values()) {
    		addSigAST(module, bufIdx, null, null, null, null, null, null, null, null);
    	}
    }

    private void createParamSigAST(DashModule module) {
        addSigAST(module, "Identifiers", null, null, null, null, null, null, null, null);
        for (DashConcState concState: module.getAllConcurrentStates().values()) {
        	if (concState.isParameterized()) {
                addSigAST(module, concState.getReplicatedIdentifier(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "Identifiers"))), null, null, null, null, null, null);
        	}
        }
    }

    /* Used by other functions to help create signature ASTs */
    private void addSigAST(DashModule module, String sigName, ExprVar isExtends, List<ExprVar> sigParent, List<Decl> decls, Pos isAbstract, Pos isLone, Pos isOne, Pos isSome, Pos isPrivate) {
        module.addSig(sigName, isExtends, sigParent, decls, null, null, AttrType.ABSTRACT.makenull(isAbstract), AttrType.LONE.makenull(isLone), AttrType.ONE.makenull(isOne), AttrType.SOME.makenull(isSome), AttrType.PRIVATE.makenull(isPrivate));
    }
    
    /****************************************** CREATE TRANSITIONS (PRE, POST, SEMANTICS, ENABLEDAFTERSTEP) ***************************************/
    
    private void createTransitionsAST(DashModule module) {
        for (DashTrans transition : module.getTransitions().values()) {
            createPreConditionAST(transition, module);
            createPostConditionAST(transition, module);
            createTransCallAST(transition, module);
            createEnabledNextStepAST(transition, module);
            createSemanticsAST(transition, module);
        }
    }
    
    /****************************************** SNAPSHOT SIGNATURE ***************************************/

    /*
     * This function creates the AST for the Snapshot signature in the Alloy model
     */
    private void createSnapshotSigAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr b = null;
        
        // conf0: StateLabel
        // conf1: Identifier -> StateLabel
        for (int tupleSize: module.getConfLevels()) {
        	b = (tupleSize == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "StateLabel")) : ExprVar.make(null, "StateLabel");
        	for (int i = 0; i < tupleSize; i++) {
        		b = DashHelper.createBinaryExpr(ExprVar.make(null, "Identifiers"), ExprBinary.Op.ARROW, b);
        	}
        	a.add(ExprVar.make(null, "conf" + tupleSize));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, b));
        	}
            a.clear();
        }  
        
        // taken0: TransitionLabel
        // taken1: Identifier -> TransitionLabel
        for (int tupleSize: module.getConfLevels()) {
        	b = (tupleSize == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "TransitionLabel")) : ExprVar.make(null, "TransitionLabel");
        	for (int i = 0; i < tupleSize; i++) {
        		b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Identifiers"), b);
        	}
        	a.add(ExprVar.make(null, "taken" + tupleSize));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, b));
        	}
            //decls.add(new Decl(null, null, null, null, a, b));
            a.clear();
        }

        // events0: EventLabel
        // events1: Identifier -> EventLabel
        for (int tupleSize: module.getEventLevels()) {
        	b = (tupleSize == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.SETOF, ExprVar.make(null, "EventLabel")) : ExprVar.make(null, "EventLabel");
        	for (int i = 0; i < tupleSize; i++) {
        		b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Identifiers"), b);
        	}
        	a.add(ExprVar.make(null, "events" + tupleSize));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, b));
        	}
            //decls.add(new Decl(null, null, null, null, a, b));
            a.clear();
        }
        
        //Create AST for variable declaration:
        //stable: one Bool
        if (module.hasHierarchy()) {
            b = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Bool"));
            a.add(ExprVar.make(null, "stable"));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, mult(b)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, mult(b)));
        	}
            //decls.add(new Decl(null, null, null, null, a, mult(b)));
            a.clear();
        }
        
        if ((!DashOptions.ctlModelChecking && !DashOptions.generateTraces) && DashOptions.generateSigAxioms) {
            b = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "Snapshot"), ExprVar.make(null, "Snapshot"));
            a.add(ExprVar.make(null, "next_step"));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, mult(b)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, mult(b)));
        	}
            //decls.add(new Decl(null, null, null, null, a, mult(b))); //next_step: Snapshot -> Snapshot
            a.clear();
        }

        /* Creating the following expression: evnVar: mappings */
        for (String variableName : module.getEnvVarExpresssion().keySet()) {
            b = module.getEnvVarExpresssion().get(variableName);
            a.add(ExprVar.make(null, variableName));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, b));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, b));
        	}
            //decls.add(new Decl(null, null, null, null, a, b));
            a.clear();
        }  
  
        /* Creating the following expression: variable: mappings (variable: param -> mapping if parameterized)*/
        for (String variableName : module.getVariableExpresssion().keySet()) {
            b = module.getVariableExpresssion().get(variableName);
            b = DashHelper.createParameterizedVar(variableName, b, module);
            a.add(ExprVar.make(null, variableName));
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, new Pos("var", 0, 0), a, convertToExprUnary(b)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, a, convertToExprUnary(b)));
        	}
            //decls.add(new Decl(null, null, null, null, a, convertToExprUnary(b)));      
            a.clear();
        }
        
        addSigAST(module, "Snapshot", null, null, decls, null, null, null, null, null);
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

        for (DashConcState concState : module.getTopLevelConcStates().values()) {
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
    	
        for (String key : module.getEvents().keySet()) {
            if (module.getEvents().get(key).getType().equals("env event"))
            	addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "EnvironmentEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
            if (module.getEvents().get(key).getType().equals("event"))
            	addSigAST(module, key, ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "InternalEvent"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
        }
    }
    
    /****************************************** TRANSITION SPACE ***************************************/


    private void createTransitionSpaceAST(DashModule module) {
    	addSigAST(module, "TransitionLabel", null, null, new ArrayList<Decl>(), new Pos("abstract", 0, 0), null, null, null, null);
        for (DashTrans transition : module.getTransitions().values()) {
        	addSigAST(module, transition.getFullyQualName(), ExprVar.make(null, "extends"), new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "TransitionLabel"))), new ArrayList<Decl>(), null, null, new Pos("one", 0, 0), null, null);
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
        addParameterizedPredicateAST(module, "pre_" + transition.getFullyQualName(), "s", null, null, null, transition.getParentConcState().getIdentifiers(), 0, expression);
    }

    /*
     * Create the pre-conditions AST and returns it. Is used both for creating the
     * pre-cond predicate and for adding pre-conditions to the
     * enabledAfterStep_transName predicate
     */
    private Expr getPreCondAST(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST
        isCreatingPreCond = true;
        Expr binaryFrom = null;
		int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();
        /* Creating the following expression: sourceState in s.conf */
        if (transition.getOrigin().getAllOrigins().size() > 0) {       
            Expr left = null;
        	for(DashState state: module.getORStates().values()){
    			String fromState = transition.getOrigin().getAllOrigins().get(0).replace('/', '_');
        		if(state.getInnerORStates().size() > 0 && state.getFullyQualName().equals(transition.getOrigin().getAllOrigins().get(0).replace('/', '_'))) {
        			left =  DashHelper.createExprVar(fromState); 
        			Expr right = DashHelper.sConf(0);
        			right = DashHelper.addParametersJoin(right, totalIEsInTree);
        			binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.INTERSECT, mult(right));
        			binaryFrom = DashHelper.createUnaryExpr(ExprUnary.Op.SOME, binaryFrom);     				
        			break;
        		}
        		else if(state.getInnerORStates().size() == 0 && state.getFullyQualName().equals(transition.getOrigin().getAllOrigins().get(0).replace('/', '_'))){
        			left =  DashHelper.createExprVar(fromState); 
        			Expr right = DashHelper.sConf(totalIEsInTree);
        			right = DashHelper.addParametersJoin(right, totalIEsInTree);
                    binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(right));
        			break;
        		}     			
        	}
        	if(binaryFrom == null) {
        		Expr right = DashHelper.sConf(0);
        		Expr source = DashHelper.createExprVar(transition.getOrigin().getAllOrigins().get(0).replace('/', '_')); 
        		binaryFrom = DashHelper.createBinaryExpr(source, ExprBinary.Op.IN,  mult(right));
        	}
        }

        /*
         * Creating the following expression: onExprName in (s.events &
         * EnvironmentEvent)
         */
        Expr binaryOn = null;
        
        String onCommand = transition.getTriggerEvent() == null ? "" : transition.getTriggerEvent().getRawName().replace('/', '_');
        int iesInEvent = (transition.getTriggerEvent() != null) ? transition.getTriggerEvent().getParentConcState().getIdentifiers().size() : 0;
        if (transition.getTriggerEvent() != null && transition.getTriggerEvent().getRawName() != null && module.hasEnvEvents() && !module.hasHierarchy()) {
        	Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.sEvents(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent); // p0.(s.events)
            Expr rightBinary = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, DashHelper.envEvent()); // s.events & EnvironmentEvent
            binaryOn = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(rightBinary)); //ExprBinary.Op.IN.make(null, null, left, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)         
        }
        
        if (transition.getTriggerEvent() != null && transition.getTriggerEvent().getRawName() != null && transition.getTriggerEvent().isInternal() && module.hasEnvEvents() && module.hasHierarchy()) {
        	Expr sStableTrue = DashHelper.createBinaryExpr(DashHelper.sStable(), ExprBinary.Op.EQUALS, DashHelper.trueExpr()); //s.stable = True
        	//Expr notSStableTrue = DashHelper.createUnaryExpr(ExprUnary.Op.NOT, sStableTrue); // !(s.stable = True)
            Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.sEvents(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent);
            Expr eventInSEvents = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(sEvents));  //onExprName in (s.events)  
            binaryOn = eventInSEvents;//ExprBinary.Op.OR.make(null, null, notSStableTrue, eventInSEvents); // !(s.stable = True) or onExprName in (s.events)          
        }
        else if (transition.getTriggerEvent() != null && transition.getTriggerEvent().getRawName() != null && module.hasEnvEvents() && module.hasHierarchy()) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True"));
            Expr left = ExprVar.make(null, onCommand);
            Expr sEvents = DashHelper.sEvents(iesInEvent); // s.events
            sEvents = DashHelper.addParametersJoin(sEvents, iesInEvent);
            Expr rightBinary = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, DashHelper.envEvent()); // s.events & EnvironmentEvent
            Expr ifExpr = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(rightBinary)); //onExprName in (s.events & EnvironmentEvent)
            Expr elseExpr = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(sEvents)); //onExprName in (s.events)  
            binaryOn = ExprITE.make(null, sStableTrue, ifExpr, elseExpr);             
        }

        expression = (binaryOn != null) ? ExprBinary.Op.AND.make(null, null, binaryFrom, binaryOn) : binaryFrom;

        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.getCondition() != null && transition.getCondition().getAllExpressions() != null) {        	
            Expr modifiedExpr = getVarFromParentExpr(transition.getCondition().getExpr(), DashHelper.getParentConcState(transition.getParent()), module);
            expression = (expression == null) ? ExprBinary.Op.AND.make(null, null, binaryFrom, modifiedExpr) : ExprBinary.Op.AND.make(null, null, expression, modifiedExpr); 
        }

        isCreatingPreCond = false;
        return expression;
    }
    
    private Expr getPreCondForEnabled(DashTrans transition, DashModule module) {
        Expr expression = null; //This is the final expression that will be stored in the predicate AST
		int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();
        Expr binaryFrom = null;
        /* Creating the following expression: sourceState in s.conf (if no inner OR states)
         * else create: some sourceState in s.conf */
        if (transition.getOrigin().getAllOrigins().size() > 0) {       
            Expr left = null;
            
        	DashState sourceState = DashHelper.getState(transition.getOrigin().getAllOrigins().get(0), module);
        	String fromExprStr = transition.getOrigin().getAllOrigins().get(0).replace('/', '_');
        	
        	if(sourceState != null && sourceState.getInnerORStates().size() > 0) {
        		left = ExprVar.make(null, fromExprStr);
        		Expr right = DashOptions.isElectrum ? DashHelper.sConfPrimed(totalIEsInTree) : DashHelper.sConf(totalIEsInTree);
    			right = DashHelper.addParametersJoin(right, totalIEsInTree);
    			binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.INTERSECT, mult(right));
    			binaryFrom = DashHelper.createUnaryExpr(ExprUnary.Op.SOME, binaryFrom); 
        	}
        	else if(sourceState != null && sourceState.getInnerORStates().size() == 0){
                left = ExprVar.make(null, fromExprStr);
                Expr right = DashOptions.isElectrum ? DashHelper.sConfPrimed(totalIEsInTree) : DashHelper.sConf(totalIEsInTree);
    			right = DashHelper.addParametersJoin(right, totalIEsInTree);
                binaryFrom = DashHelper.createBinaryExpr(left, ExprBinary.Op.IN, mult(right));
        	}     			
        	
        	if(binaryFrom == null) {
        		Expr right = DashOptions.isElectrum ? DashHelper.sConfPrimed(totalIEsInTree) : DashHelper.sConf(totalIEsInTree);
        		right = DashHelper.addParametersJoin(right, totalIEsInTree);
        		Expr source = ExprVar.make(null, fromExprStr);
        		binaryFrom = ExprBinary.Op.IN.make(null, null, source, mult(right));
        	}	
        }

        expression = binaryFrom;

        isCreatingEnabledAfterPred = true;
        
        /* Creating the following expression: AND[whenExpr, whenExpr, ..] */
        if (transition.getCondition() != null && transition.getCondition().getAllExpressions() != null) {           	
            Expr modifiedExpr = getVarFromParentExpr(transition.getCondition().getExpr(), DashHelper.getParentConcState(transition.getParent()), module);
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
    	// get the parent state in which the post-condition for this transition is situated
    	DashConcState parent = DashHelper.getParentConcState(transition.getParent());
    	// the final expression to be enclosed in the predicate
    	Expr expression = null;
    	// get the number of nested identifier elements in the transitions's parent state
    	int totalIEsInTree = transition.getParentConcState().getIdentifiers().size();

    	/*
    	* Creating the following expression: s_next.conf = s.conf - sourceState +
    	* destinationState
    	*/
    	if (transition.getDestination().getAllDestinations().size() > 0) {
        	// Stores the destination state
        	String gotoExprStr = transition.getDestination().getAlloyName();         
        	// Stores the origin state
          String fromExprStr = (DashHelper.getState(transition.getOrigin().getAlloyName(), module) != null) ? 
            		DashHelper.getState(transition.getOrigin().getAlloyName(), module).getFullyQualName() : transition.getOrigin().getAlloyName();
           
    	Expr fromExpr = DashHelper.createExprVar(fromExprStr); // Origin State
    	Expr gotoExpr = DashHelper.createExprVar(gotoExprStr); // Destination State
    	gotoExpr = DashHelper.addParametersArrow(gotoExpr, totalIEsInTree); // ie -> State
    	fromExpr = DashHelper.addParametersArrow(fromExpr, totalIEsInTree); // ie -> State
            
    	// Stores the origin and destination states for this transition (mapping from level to state)
        	Map<Integer, Expr> conf2GotoExpr = new LinkedHashMap<Integer, Expr>();
        	Map<Integer, Expr> conf2FromExpr = new LinkedHashMap<Integer, Expr>();
        	
    	/* If we are transitioning into a state with concurrent states */
    	if (transition.getDestination().getAllDestinations() != null && transition.getDestination().getAllDestinations().size() > 0) {
    		conf2GotoExpr = new LinkedHashMap<Integer, Expr>(DashHelper.calculateConf2GotoExpr(transition));
    	}
            
            /* If we are transitioning out of a concurrent state */
            if (transition.getOrigin().getAllOrigins() != null && transition.getOrigin().getAllOrigins().size() > 0) {
            	conf2FromExpr = new LinkedHashMap<Integer, Expr>(DashHelper.calculateConf2FromExpr(transition));
            }
            
            /* 
             * Creating the following expression: 
             * s_next.conf(i) = s.conf(i) + (p0 -> State) + ....
             * s_next.conf(i + 1) = s.conf(i + 1) + (p0 -> p1 -> State) + ....
             */
            for (int i: module.getConfLevels()) {
                Expr sConf = DashHelper.createExprBadJoin("s", "conf" + i); //s.conf
                Expr sConfPrime = DashHelper.createExprBadJoin("s_next", "conf" + i); //s_next.conf
                
                sConf = !(transition.getOrigin().isTransitionToParentState()) && (totalIEsInTree == i) ? 
                		DashHelper.createBinaryExpr(sConf, ExprBinary.Op.MINUS, fromExpr) : sConf; // s.conf - (p0 -> State) - (...)
                sConf = !(transition.getDestination().isEnteringDefaultState()) && (totalIEsInTree == i) ?
                		DashHelper.createBinaryExpr(sConf, ExprBinary.Op.PLUS, gotoExpr) : sConf; // s.conf + (p0 -> State) + (...)
                
                if (conf2FromExpr.containsKey(i)) {
                	sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.MINUS, conf2FromExpr.get(i)); //s.conf - (IE -> State)
                }
                if (conf2GotoExpr.containsKey(i)) {
                	sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.PLUS, conf2GotoExpr.get(i)); //s.conf + (IE -> State)
                }

                if (sConf == null) {
                	throw new NullPointerException("There is a null expression (sConf) in the post-condition.");
                }
                sConfPrime = DashHelper.createBinaryExpr(sConfPrime, ExprBinary.Op.EQUALS, sConf); // s_next.conf = s.conf - ... + ...
                expression = (expression == null) ? sConfPrime : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sConfPrime);
            }
        }

        /* 
         * Creating the following expression: AND[doexpr, doexpr, ..] 
         */
        if (expression == null) {
        	throw new NullPointerException("There is a null expression (sConf) in the post-condition.");
        }
        
        if (transition.getActions() != null && transition.getActions().getAllExpression() != null) {               
            Expr exprWithFullyQualNames = getVarFromParentExpr(transition.getActions().getExpr(), DashHelper.getParentConcState(transition.getParent()), module);                 
            expression =  DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, exprWithFullyQualNames);
            
            //These are the variables that have not been changed in the post-cond and they need to retain their values in the next snapshot
            Map<String, DashConcState> unchangedVars = new LinkedHashMap<String, DashConcState>(getUnchangedVars(transition.getActions().getAllExpression(), module));
            
            for (String var: changedLocalVars.keySet()) {
            	// We do not constrain a var if it has been changed using a reference, otherwise we constrain it if it only has been changed locally
            	expression = (changedRefVars.contains(var) || (changedLocalVars.get(var).getIdentifiers().size() == 0) ) ? 
            			expression : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, constrainLocallyChangedVars(var, changedLocalVars.get(var)));
            }
            for (String var : unchangedVars.keySet()) {
                expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, createUnchangedVariableAST(var, unchangedVars.get(var), parent));
            }
            clearVarChangeContainers();
        }
        
        /* Creating the following expression(s): s_next.variable = s.variable */
        if (transition.getActions() == null) {
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
        if (module.hasHierarchy() && !module.hasEnvEvents()) {
        	Expr sNextStable =  DashHelper.sNextStable();
        	Expr ifExpr = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr());
            Expr ElseExpr = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.falseExpr());
            Expr ifCond = DashHelper.createExprBadJoin("s", "testIfNextStable"); 
            ifCond = DashHelper.createExprBadJoin("s_next", ifCond);
            ifCond = DashHelper.createExprBadJoin(transition.getFullyQualName(), ifCond);
            ifCond =DashHelper.createExprBadJoin("none", ifCond);
            
            /* Conjunction of any env variables in the model */
            for(String concStateName: module.getEventVarNames().keySet()) {
            	for(String envVar: module.getEventVarNames().get(concStateName)) {
            		Expr leftJoin = DashHelper.createExprBadJoin(DashHelper.sNext(), concStateName + "_" + envVar) ;
            		Expr rightJoin = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar(concStateName + "_" + envVar));
            		Expr equals = DashHelper.createBinaryExpr(leftJoin, ExprBinary.Op.EQUALS, rightJoin);
            		ElseExpr = DashHelper.createBinaryExpr(ElseExpr, ExprBinary.Op.AND, equals);
            	}
            }
            
            Expr ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);
            expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, ifElseExpr);
        }
        
        /*
         * Creating the following expression: testIfNextStable[s, s_next, {none},
         * Elevator_Controller_sendReq] => { s_next.stable = True s.stable = True => { no
         * ((s_next.events & InternalEvent) ) } else { no ((s_next.events & InternalEvent) - {
         * (InternalEvent & s.events)}) } } else { s_next.stable = False s.stable = True =>
         * { s_next.events & InternalEvent = {none}/sendExpr s_next.events & EnvironmentEvent = s.events
         * & EnvironmentEvent } else { s_next.events = s.events + {none}/sendExpr } }
         */
        Expr sendExpr = null;
        if (module.hasHierarchy() && module.hasEnvEvents()) {
        	String sendStr = transition.getEventTriggered() == null ? "" : transition.getEventTriggered().getRawName().replace('/', '_');
        	int iesInEvent = transition.getEventTriggered() != null ? transition.getEventTriggered().getParentConcState().getIdentifiers().size() : 0;
        	Expr sNextStable = DashHelper.sNextStable(); //s_next.stable
        	Expr sPrimeStableTrue = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr()); //s_next.stable = True
        	Expr sPrimeStableFalse = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.falseExpr()); //s_next.stable = False
            Expr sStableTrue = DashHelper.createBinaryExpr(DashHelper.sStable(), ExprBinary.Op.EQUALS,  DashHelper.trueExpr()); //s.stable = False
            
            if(transition.getEventTriggered() != null && transition.getEventTriggered().getRawName() != null) {
            	if(transition.getEventTriggered().getEventsTriggered() != null) {
            		sendExpr = DashHelper.createBinaryExpr(getVarFromParentExpr(transition.getEventTriggered().getEventsTriggered(), transition.getEventTriggered().getParentConcState(), module), 
            				ExprBinary.Op.ARROW, DashHelper.createExprVar(sendStr));
            		sendExpr = DashHelper.addParametersArrow(sendExpr, iesInEvent - 1);
            	}
            	else {
            		sendExpr = DashHelper.createExprVar(sendStr);
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
            for (int key: module.getEventLevels()) {
            	Expr noneToNone = DashHelper.addIdentifiersNone(DashHelper.createExprVar("none"), key);
            	sendExprCom = (key == iesInEvent) ? sendExpr : noneToNone;
            	sendExprCom = (sendExprCom == null) ? noneToNone : sendExprCom;
            	Expr intEvent = DashHelper.intEvent();
            	intEvent = DashHelper.addIdentifiersArrow(intEvent, key); // s.events
                Expr sEvents = DashHelper.sEvents(key); // s.events
                Expr sNextEvents = DashHelper.sNextEvents(key); // s_next.events
                Expr sEnvAndIntEvn = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, intEvent); //s.events & InternalEvent
                Expr sNextEnvAndIntEvn = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, intEvent); //s_next.events & InternalEvent
                Expr ifLowerIf = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, sendExprCom); //s_nextevents & InternalEvent = sendEvent
            	sPrimeEnvAndIntEvnEqualsEvn = (sPrimeEnvAndIntEvnEqualsEvn == null) ? 
            			ifLowerIf : DashHelper.createBinaryExpr(sPrimeEnvAndIntEvnEqualsEvn, ExprBinary.Op.AND ,ifLowerIf); //sendEvent (or none) & (s.events & InternalEvent)
                Expr ifLowerElse = DashHelper.createBinaryExpr(sendExprCom, ExprBinary.Op.PLUS, sEnvAndIntEvn);
                ifLowerElse = (transition.getEventTriggered() == null) ? sEnvAndIntEvn : ifLowerElse;
                Expr sNextIntEqualSendAndInt = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, ifLowerElse); //s_next.events & InternalEvent = sendEvent (or none) + (s.events & InternalEvent)
                sPrimeEvnIntEvnEqualsSend = (sPrimeEvnIntEvnEqualsSend == null) ? 
                		sNextIntEqualSendAndInt : DashHelper.createBinaryExpr(sPrimeEvnIntEvnEqualsSend, ExprBinary.Op.AND ,sNextIntEqualSendAndInt);;           

                Expr elseLowerExprIf = DashHelper.createBinaryExpr(sNextEnvAndIntEvn, ExprBinary.Op.EQUALS, sendExprCom); //s_next.events & InternalEvent = {sendEvent}  
                Expr envEvent = DashHelper.envEvent();
                envEvent = DashHelper.addIdentifiersArrow(envEvent, key);
                Expr sPrimeEvtAndEnv = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, envEvent); //s_next.events & EnvironmentEvent
                Expr sEventAndEnv = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.INTERSECT, envEvent); //s.events & EnvironmentEvent
                elseLowerExprIf = DashHelper.createBinaryExpr(elseLowerExprIf, ExprBinary.Op.AND, DashHelper.createBinaryExpr(sPrimeEvtAndEnv, ExprBinary.Op.EQUALS, sEventAndEnv));
                sNextEvnEqlSEnv = (sNextEvnEqlSEnv == null) ? elseLowerExprIf : DashHelper.createBinaryExpr(sNextEvnEqlSEnv, ExprBinary.Op.AND, elseLowerExprIf);

                Expr elseLowerElse = null;
                Expr sEventsPlusSend = DashHelper.createBinaryExpr(sEvents, ExprBinary.Op.PLUS, sendExprCom);
                elseLowerElse = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.EQUALS, sEventsPlusSend); //s_next.events = s.events + none
                elseLowerElse = (transition.getEventTriggered() == null) ? 
                		DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.EQUALS, sEvents) : DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.EQUALS, sEventsPlusSend); 
                sEnvEqEnvPlusSend = (sEnvEqEnvPlusSend == null) ? elseLowerElse : DashHelper.createBinaryExpr(sEnvEqEnvPlusSend, ExprBinary.Op.AND, elseLowerElse);
            }
            
            if (sPrimeEnvAndIntEvnEqualsEvn == null || sPrimeEvnIntEvnEqualsSend == null || sNextEvnEqlSEnv == null || sEnvEqEnvPlusSend == null) {
            	throw new NullPointerException("There is a null expression (testIfNextStable) in the post-condition.");
        	}
            ifLowerExpr = ExprITE.make(null, sStableTrue, sPrimeEnvAndIntEvnEqualsEvn, sPrimeEvnIntEvnEqualsSend);
            ifLowerExpr = DashHelper.createBinaryExpr(sPrimeStableTrue, ExprBinary.Op.AND, ifLowerExpr);         
            elseLowerExpr = ExprITE.make(null, sStableTrue, sNextEvnEqlSEnv, sEnvEqEnvPlusSend);
            elseLowerExpr = DashHelper.createBinaryExpr(sPrimeStableFalse, ExprBinary.Op.AND, elseLowerExpr);
         
            /* Conjunction of any env variables in the model 
             * s_next.envVar = s.envVar
             */
            for(String concStateName: module.getEventVarNames().keySet()) {
            	for(String envVar: module.getEventVarNames().get(concStateName)) {
            		Expr leftJoin = DashHelper.createExprBadJoin(DashHelper.sNext(), DashHelper.createExprVar(concStateName + "_" + envVar)); //s_next.envVar
            		Expr rightJoin = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar(concStateName + "_" + envVar)); // s.envVar
            		Expr equals = DashHelper.createExprBadJoin(leftJoin, rightJoin); // s_next.envVar = s.envVar
            		elseLowerExpr = DashHelper.createBinaryExpr(elseLowerExpr, ExprBinary.Op.AND, equals);
            	}
            }
            
            // Get the level of nesting for any events triggered
            int iesInOnEvent = 0, iesInSendEvent = 0;
            if (transition.getTriggerEvent() != null && transition.getTriggerEvent().getRawName() != null) {
            	iesInOnEvent = transition.getTriggerEvent().getParentConcState().getIdentifiers().size();
            }
            if (transition.getEventTriggered() != null && transition.getEventTriggered().getRawName() != null) {
            	iesInSendEvent = transition.getEventTriggered().getParentConcState().getIdentifiers().size();
            }
            
            Expr tFuncCall = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar("testIfNextStable" + iesInSendEvent)); //s.testIfNextStable
            Expr genEventT = DashHelper.createExprBadJoin(DashHelper.sNext(), tFuncCall); //s_next.s.enabledAfterStep_transName
            Expr sPrimeGenEventT = DashHelper.createExprBadJoin(DashHelper.createExprVar(transition.getFullyQualName()), genEventT); //tranName.s_next.s.enabledAfterStep_transName
            sendExprCom = (sendExpr == null) ? DashHelper.createExprVar("none") : sendExpr;
            Expr ssPrimeGenEventT = DashHelper.createExprBadJoin(sendExprCom, sPrimeGenEventT); // sendEventName.tranName. s_next.s.enabledAfterStep_transName
            expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, ExprITE.make(null, ssPrimeGenEventT, ifLowerExpr, elseLowerExpr));
            
            if (!eventSize2Trans.containsKey(iesInOnEvent)) {
            	eventSize2Trans.put(iesInOnEvent, new ArrayList<DashTrans>());
            	eventSize2Trans.get(iesInOnEvent).add(transition);
            }
            else {
            	eventSize2Trans.get(iesInOnEvent).add(transition);
            }  
        }
        
        /* Creating the following expression: no (s_next.events & InternalEvent) */
        Expr sendComExpr = null;
        if (transition.getEventTriggered() == null && module.hasEnvEvents() && !module.hasHierarchy()) {
            for (int key: module.getEventLevels()) { 
            	Expr sNextEvents =  DashHelper.sNextEvents(key);  //s_next.events & InternalEvent
            	Expr sNextEnvAndIntEvn = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.INTERSECT, DashHelper.intEvent()); //s_next.events & InternalEvent
            	Expr noEvents = DashHelper.createUnaryExpr(ExprUnary.Op.NO, sNextEnvAndIntEvn);
            	sendComExpr = (sendComExpr == null) ? noEvents : DashHelper.createExprBadJoin(sendComExpr, noEvents); // no (s_next.events & InternalEvent)
            }
        }
        
        /* Creating the following expression: sentEvent in s_next.events */
        if (transition.getEventTriggered() != null && transition.getEventTriggered().getRawName() != null && sendExpr != null) {
        	int i = transition.getEventsTriggered().getParentConcState().getIdentifiers().size();
        	Expr sNextEvents = DashHelper.sNextEvents(i);
        	sendComExpr = DashHelper.createBinaryExpr(sendExpr, ExprBinary.Op.IN, sNextEvents); // sentEvent in s_next.events
        }

        if (sendComExpr != null) {
            expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sendComExpr);
        }
           
        /* For managing Enter/Exit commands */        
        DashState destinationState = getState(transition.getDestination().getAllDestinations().get(0).replace('/', '_'), module);
        if(transition.getDestination().getAllDestinations().size() > 0 && destinationState != null) {        	
        	Expr gotoExpr = DashHelper.createExprVar(transition.getDestination().getAllDestinations().get(0).replace('/', '_'));
        	Expr enterCall = DashHelper.createExprBadJoin(DashHelper.sNext(), DashHelper.createExprVar( "enter_" + gotoExpr.toString()));
        	
        	if(destinationState.getEnters().size() > 0) {
        		expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, enterCall);
        	}
        } 
        
        DashState sourceState = getParentSourceState(transition, module);
        expression = createExitAST(expression, sourceState, transition);        
        expression = ExprUnary.Op.NOOP.make(null, expression);
       
        addParameterizedPredicateAST(module, "pos_" + transition.getFullyQualName(), "s", "s_next", null, null, transition.getParentConcState().getIdentifiers(), 0, expression);
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
        Expr sNextTaken = DashOptions.isElectrum ? DashHelper.sTakenPrimed(totalIEsSize) : DashHelper.sNextTaken(totalIEsSize); //s_next.taken
        Expr sTaken = DashHelper.sTaken(totalIEsSize); //s.taken
        if (!module.hasHierarchy()) {
            semanticsExpr = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ExprVar.make(null, transition.getFullyQualName())); //s_next.taken = currentTrans
            expression = semanticsExpr;
        }
              
        List<DashTrans> innerTransitions = new ArrayList<DashTrans>();
        if(!module.hasHierarchy()) {
        	if(transition.getParent() instanceof DashState && ((DashState) transition.getParent()).getInnerORStates().size() > 0){
        		for(DashState state: ((DashState) transition.getParent()).getInnerORStates())
        			DashHelper.getInnerTransitions(state, innerTransitions);	
        	}
        	
        	for(DashTrans trans: innerTransitions) 
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.getFullyQualName()))));	
        }
        
        /*
         * Creating the following expression: s.stable = True => (s_next.taken + transName)
         * else { )
         */
        Expr ifElseExpr = null;
        if (module.hasHierarchy()) {
            Expr ifCond = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable")), ExprVar.make(null, "True")); //s.stable = True
            Expr ifRight = transNameExpr; // transName
            for (int i = totalIEsSize - 1; i >= 0; i--) {
            	ifRight = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), ifRight);
            }
            Expr ifExpr = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ifRight); //s_next.taken = currentTrans
            Expr noTaken = DashHelper.noTakenSemanticsConstraints("taken", totalIEsSize, module);
            ifExpr = (noTaken == null) ? ifExpr : DashHelper.createBinaryExpr(ifExpr, ExprBinary.Op.AND, noTaken); //no s_next.taken1 and no s_next.taken2
            
            Expr ElseExprLeft = ExprBinary.Op.EQUALS.make(null, null, sNextTaken, ExprBinary.Op.PLUS.make(null, null, sTaken, ifRight)); // s_next.taken0 = s.taken0 + transName or s_next.taken = s.taken + (p0 -> p1 -> currentTrans)
            Expr takenEquals = DashHelper.constraintEquals("taken", totalIEsSize, module);
            ElseExprLeft = (takenEquals == null) ? ElseExprLeft : DashHelper.createBinaryExpr(ElseExprLeft, ExprBinary.Op.AND, takenEquals); //s_next.taken1 = s.taken1
            
            Expr elseExprRight = null;
            Expr elseRightBinPlus = null;
            
            DashConcState transParent = DashHelper.getParentConcState(transition.getParent());
            Expr orthagonality = null;
            for (int key: transParent.getAllChildConcStates().keySet()) {
        		if (key == 0) {
	            	for (DashConcState child: transParent.getAllChildConcStates().get(key)) {
	                    for (DashTrans trans : child.getAllTransitions()) {
	                    	String transitionName = trans.getFullyQualName();
	                        if (elseRightBinPlus == null) {
	                        	elseRightBinPlus = ExprVar.make(null, transitionName);
	                        }
	                        else {
	                        	elseRightBinPlus = ExprBinary.Op.PLUS.make(null, null, elseRightBinPlus, ExprVar.make(null, transitionName));
	                        }
	                    
	                    }
	            	}
	                if (elseRightBinPlus != null) {
	                	Expr sTaken0 = DashHelper.sTaken(0);
	    	            elseExprRight = ExprBinary.Op.INTERSECT.make(null, null, sTaken0, elseRightBinPlus); // (s.taken & transNames)
	    	            elseExprRight = ExprUnary.Op.NO.make(null, elseExprRight); // no (s.taken & transNames)
	    	            orthagonality = elseExprRight;
	                }
        		}
        		else {
        			boolean orthogonalAdded = false;
	            	for (DashConcState child: transParent.getAllChildConcStates().get(key)) {
	                    if (child.getFullyQualName().equals(transParent.getFullyQualName())) {
	                        Expr staken = DashHelper.sTaken(key);
	                        Expr pSTaken = DashHelper.addParametersJoin(staken, totalIEsSize); 
	                        Expr noPTaken = ExprUnary.Op.NO.make(null, pSTaken);
	                        orthagonality = (orthagonality == null) ? noPTaken : DashHelper.createBinaryExpr(orthagonality, ExprBinary.Op.AND, noPTaken);
	                    }
	                    else {
	                    	if (orthogonalAdded && totalIEsSize > 0) continue;
	                        Expr staken = DashHelper.sTaken(key);
	                        Expr pSTaken = totalIEsSize == 0 ? staken : DashHelper.addParametersJoin(staken, totalIEsSize - 1); //p0.sTaken1
	                        Expr var = totalIEsSize == 0 ? DashHelper.createExprVar(child.getTopParentRepConcState().getReplicatedIdentifier()) : DashHelper.createExprVar("p" + (totalIEsSize - 1));
	                        Expr pDomSTaken = DashHelper.createBinaryExpr(var, ExprBinary.Op.DOMAIN, pSTaken);
	                        Expr neg = DashHelper.createUnaryExpr(ExprUnary.Op.NO, pDomSTaken); // no (p0 <: taken2) or no (p1 <: p0.taken3)
	                        orthagonality = (orthagonality == null) ? neg : DashHelper.createBinaryExpr(orthagonality, ExprBinary.Op.AND, neg);
	                    }
                        orthogonalAdded = true;
	            	}
        		}
            }
            
            Expr ElseExpr = (orthagonality == null) ? ElseExprLeft : DashHelper.createBinaryExpr(ElseExprLeft, ExprBinary.Op.AND, orthagonality);

            ifElseExpr = ExprITE.make(null, ifCond, ifExpr, ElseExpr);                      
            expression = ifElseExpr;
            
        	if(transition.getParent() instanceof DashState && ((DashState) transition.getParent()).getInnerORStates().size() > 0){
        		for(DashState state: ((DashState) transition.getParent()).getInnerORStates())
        			DashHelper.getInnerTransitions(state, innerTransitions);	
        	}
        	
        	for(DashTrans trans: innerTransitions) {
        		expression = ExprBinary.Op.AND.make(null, null, expression, ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "pre_" + trans.getFullyQualName()))));
        	}
        }
        
        expression = ExprUnary.Op.NOOP.make(null, expression);
        
        addParameterizedPredicateAST(module, "semantics_" + transition.getFullyQualName(), "s", "s_next", null, null, transition.getParentConcState().getIdentifiers(), 0, expression);
    }
    
    /****************************************** TRANSITION CALL PREDICATE ***************************************/

    /*
     * This function creates the AST for the transition call (the one that refers to
     * the pre,post,semantics) predicate in the Alloy Model
     */
    private void createTransCallAST(DashTrans transition, DashModule module) {
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
        int totalIEsSize = transition.getParentConcState().getIdentifiers().size();
        Expr expression = null;

        /*
         * Creating the following expressions: post_transName[s, s_next],
         * semantics_transName[s, s_next], pre_transName[s]
         */
        Expr preTransCall = ExprBadJoin.make(null, null, s, DashHelper.createExprVar("pre_" + transition.getFullyQualName())); //s.pre_transName
        preTransCall = DashHelper.addParametersJoin(preTransCall, totalIEsSize);
    
        Expr postTransCall = ExprBadJoin.make(null, null, s, DashHelper.createExprVar("pos_" + transition.getFullyQualName())); //s.post_transName
        postTransCall = DashOptions.isElectrum ? postTransCall : DashHelper.createExprBadJoin(sPrime, postTransCall); //s_next.s.post_transName
    	postTransCall = DashHelper.addParametersJoin(postTransCall, totalIEsSize); //p.s.pre_transName (For Parameterized Concurrent States)
    	
        expression = DashHelper.createBinaryExpr(preTransCall, ExprBinary.Op.AND, postTransCall); //AND[postTransCall, semanticsCall]

        Expr sematicsCall = ExprBadJoin.make(null, null, s, DashHelper.createExprVar("semantics_" + transition.getFullyQualName())); //s.sematics_transName
        sematicsCall = DashOptions.isElectrum ? sematicsCall : DashHelper.createExprBadJoin(sPrime, sematicsCall); //s_next.s.sematics_transName
    	sematicsCall = DashHelper.addParametersJoin(sematicsCall, totalIEsSize); //p.s.pre_transName (For Parameterized Concurrent States)
    	
        expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sematicsCall); //AND[postTransCall, semanticsCall, preTransCall]
        
        addParameterizedPredicateAST(module, transition.getFullyQualName(), "s", "s_next", null, null, transition.getParentConcState().getIdentifiers(), 0, expression); // (For Parameterized Concurrent States)
    }
    
    /****************************************** ENABLED AFTER STEP PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * enabledAfterStep_transName[_s, s: Snapshot] {expressions}
     */
    private void createEnabledNextStepAST(DashTrans transition, DashModule module) {
        Expr expr = null;
        if (module.hasHierarchy()) {
            expr = getPreCondForEnabled(transition, module); //Store all the pre-conditions
            int totalIEsSize = transition.getParentConcState().getIdentifiers().size();
            DashConcState transitionParent = DashHelper.getParentConcState(transition.getParent());
            Expr _sStable = (DashOptions.isElectrum) ? DashHelper.sStable() : DashHelper._sStable();
            Expr ifCond = DashHelper.createBinaryExpr(_sStable, ExprBinary.Op.EQUALS, DashHelper.trueExpr()); //_s.stable = True; 

            Expr t = ExprVar.make(null, "t");         
            Expr _sTaken = (DashOptions.isElectrum) ? DashHelper.sTaken(0) : DashHelper._sTaken(0);
            Expr _sTakenPlusT = ExprBinary.Op.PLUS.make(null, null, _sTaken, ExprVar.make(null, "t")); //_s.taken + t
            
            Expr ifExpr = null;
            Expr elseExpr = null;
            Expr conjuncts = null;
            // ORTHOGONALITY (no p0.taken1 and ...)
            for (int key: transitionParent.getAllChildConcStates().keySet()) {
        		if (key == 0) {
	            	for (DashConcState child: transitionParent.getAllChildConcStates().get(key)) {
	                    for (DashTrans trans : child.getAllTransitions()) {
	                    	Expr transitionName = DashHelper.createExprVar(trans.getFullyQualName());
	                        if (conjuncts == null)
	                        	conjuncts = transitionName;
	                        else
	                        	conjuncts = DashHelper.createBinaryExpr(conjuncts, ExprBinary.Op.PLUS, transitionName);
	                    }
	            	}
	                if (conjuncts != null) {
	                	ifExpr = ExprBinary.Op.INTERSECT.make(null, null, t, conjuncts);
	                	ifExpr = ExprUnary.Op.NO.make(null, ifExpr);
	                	elseExpr = ExprBinary.Op.INTERSECT.make(null, null, _sTakenPlusT, conjuncts);
	                	elseExpr = ExprUnary.Op.NO.make(null, elseExpr);
	                }
        		}
        		else {
        			boolean orthogonalAdded = false;
	            	for (DashConcState child: transitionParent.getAllChildConcStates().get(key)) {
	            		// no p0.taken1 where p0 is taking the transition or no p0.p1.taken2 where p1 is taking a transition or ...
	                    if (child.getFullyQualName().equals(transitionParent.getFullyQualName())) {
	                        Expr staken = DashHelper.sTaken(key);
	                        Expr pSTaken = DashHelper.addParametersJoin(staken, child.getIdentifiers().size()); 
	                        Expr noPTaken = ExprUnary.Op.NO.make(null, pSTaken);
	                        ifExpr = (ifExpr == null) ? noPTaken : DashHelper.createBinaryExpr(ifExpr, ExprBinary.Op.AND, noPTaken);
	                        elseExpr = (elseExpr == null) ? noPTaken : DashHelper.createBinaryExpr(elseExpr, ExprBinary.Op.AND, noPTaken);
	                    }
	                    // For nested replicateed components, no (p0 <: taken2) or (no p0.taken3) or...
	                    else if (child.getIdentifiers().size() > transitionParent.getIdentifiers().size()){
	                    	if (orthogonalAdded && totalIEsSize > 0) continue;
	                        Expr staken = DashHelper.sTaken(key);
	                        Expr pSTaken = totalIEsSize == 0 ? staken : DashHelper.addParametersJoin(staken, totalIEsSize - 1); //p0.sTaken1
	                        Expr var = totalIEsSize == 0 ? DashHelper.createExprVar(child.getTopParentRepConcState().getReplicatedIdentifier()) : DashHelper.createExprVar("p" + (totalIEsSize - 1));
	                        Expr pDomSTaken = DashHelper.createBinaryExpr(var, ExprBinary.Op.DOMAIN, pSTaken);
	                        Expr neg = DashHelper.createUnaryExpr(ExprUnary.Op.NO, pDomSTaken); // no (p0 <: taken2) or no (p1 <: p0.taken3)
	                        ifExpr = (ifExpr == null) ? neg : DashHelper.createBinaryExpr(ifExpr, ExprBinary.Op.AND, neg);
	                        elseExpr = (elseExpr == null) ? neg : DashHelper.createBinaryExpr(elseExpr, ExprBinary.Op.AND, neg);
	                    }
	                    orthogonalAdded = true;
	            	}
        		}
            }
           
            String onCommand = transition.getTriggerEvent() == null ? "" : transition.getTriggerEvent().getRawName().replace('/', '_');
            int totalIEsSizeSend = (transition.getTriggerEvent() == null) ? 0 : transition.getTriggerEvent().getParentConcState().getIdentifiers().size();
            if (module.hasEnvEvents() && transition.getTriggerEvent() != null && transition.getTriggerEvent().getRawName() != null) {
                Expr _sEvent = DashOptions.isElectrum ? DashHelper.sEvents(totalIEsSizeSend) : DashHelper._sEvents(totalIEsSizeSend);
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
            
            addParameterizedPredicateAST(module, "enabledAfterStep_" + transition.getFullyQualName(), "_s", "s", "t", "genEvents", transition.getParentConcState().getIdentifiers(), totalIEsSizeSend, expr);
        }
    }
    
    /****************************************** STABLE PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred stable[s] {
     * s.stable }
     */
    private void createStableAST(DashModule module) {
        Expr sStable = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "stable"));
        Expr sStableEqualsTrue = ExprBinary.Op.EQUALS.make(null, null, sStable, ExprVar.make(null, "True"));
        if (module.hasHierarchy()) {
        	addPredicateAST(module, "stable", "s", null, null, null, sStableEqualsTrue);
        }
    }
    
    /****************************************** SMALL STEP PREDICATE ***************************************/
    
    /*
    *  This function creates an AST for the following predicate: pred operation[s,
    *  s_next: Snapshot] { expressions }
    */
    void createSmallStepAST(DashModule module) {
        Expr expression = null;
        for (DashTrans trans : module.getTransitions().values()) {
        	int iesSize = trans.getParentConcState().getIdentifiers().size();
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            a.add(ExprVar.make(null, "p" + i));
	            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	            a.clear();
            }
            
            Expr expr = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, trans.getFullyQualName()));
            expr = (DashOptions.isElectrum) ? expr :  ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), expr);
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
            	expr = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), expr);
            }
            expr = (iesSize == 0) ? expr : ExprQt.Op.SOME.make(null, null, decls, expr); // some p: param | transName[s, s_next, p]
            expression = (expression == null) ? expr : ExprBinary.Op.OR.make(null, null, expression, expr);
        }
        
        Expr isEnabled = DashHelper.createExprVar("isEnabled");
        isEnabled = DashHelper.createExprBadJoin(DashHelper.sNext(), isEnabled);
        
        Expr equalsCall = DashHelper.createExprVar("equals");
        equalsCall = DashHelper.createExprBadJoin(DashHelper.s(), equalsCall);
        equalsCall = (DashOptions.isElectrum) ? equalsCall : DashHelper.createExprBadJoin(DashHelper.sNext(), equalsCall);
        
        expression = (DashOptions.createLoop && DashOptions.ctlModelChecking) ? DashHelper.createImplesElseExpr(isEnabled, expression, equalsCall) : expression;
       
        addSmallStepPredicateAST(module, "small_step", "s", "s_next", expression);
    }
    
    /****************************************** PATH PREDICATE ***************************************/
    
    private void createPathAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sPrime = ExprVar.make(null, "s_next");
        List<ExprVar> a = new ArrayList<ExprVar>(Arrays.asList(s)); //[s]
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr sNext = DashOptions.ctlModelChecking ? ExprBadJoin.make(null, null, s, ExprVar.make(null, "ks_sigma")) : ExprBadJoin.make(null, null, s, ExprVar.make(null, "next")); //s.next

        Expr expression = null;

        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        a = new ArrayList<ExprVar>(Arrays.asList(sPrime));
        decls.add(new Decl(null, null, null, null, a, mult(sNext))); //s_next: s.next

        Expr operationCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));
        operationCall = ExprBadJoin.make(null, null, sPrime, operationCall); //s_next.s.operation

        expression = ExprQt.Op.ALL.make(null, null, decls, operationCall);

        decls.clear();
        a = new ArrayList<ExprVar>(Arrays.asList(s)); //[s]
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr ctlInitCall = createInitCall(module, false);
        ctlInitCall = ExprQt.Op.SOME.make(null, null, decls, ctlInitCall);
        expression = DashOptions.ctlModelChecking ? ExprBinary.Op.AND.make(null, null, expression, ctlInitCall) : ExprBinary.Op.AND.make(null, null, expression, createInitCall(module, true));
        addPredicateAST(module, "path", null, null, null, null, expression);
    }
    
    /****************************************** TEST IF STABLE PREDICATE ***************************************/

    /*
     * This function creates an AST for the following predicate: pred
     * testIfNextStable[s, s_next: Snapshot, genEvents: set InternalEvent,
     * t:TransitionLabel] {}
     */
    private void createTestIfStableAST(DashModule module) {
    	if (eventSize2Trans.size() != 0) {
	        for (int key : eventSize2Trans.keySet()) {
	        	Expr expr = null;
	        	//System.out.println("Checking: " + key + " Contains?: " + eventSize2Trans.containsKey(key));
	        	if (eventSize2Trans.containsKey(key)) {
		        	for (DashTrans trans: eventSize2Trans.get(key)) {
			            List<Decl> decls = new ArrayList<Decl>();
			            List<ExprVar> a = new ArrayList<ExprVar>();
			            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
			                a.add(ExprVar.make(null, "p" + i));
			                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
			                a.clear();
			            }
			            
			           	Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.getFullyQualName())); //t.enabledAfterStep_transName
			            Expr genEventT = (DashOptions.isElectrum) ? tFuncCall : ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
			            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
			            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
			            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
			            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), ssPrimeGenEventT);
			            }
			            
			            Expr quant = (trans.getParentConcState().getIdentifiers().size() == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.NOT, ssPrimeGenEventT) : ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventT);
			            expr = (expr == null) ? quant : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, quant) ; // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
		        	}
	        	}
	        	expr = addOtherTestIfState(module, key, expr);
	            expr = ExprUnary.Op.NOOP.make(null, expr); 
	            addPredicateAST(module, "testIfNextStable" + key, "s", "s_next", "t", "genEvents", key, expr);
	    	}
    	}
        
        /* For models without any events */
        if (eventSize2Trans.size() == 0) {
        	Expr expr = null;
        	for (DashTrans trans: module.getTransitions().values()) {
	            List<Decl> decls = new ArrayList<Decl>();
	            List<ExprVar> a = new ArrayList<ExprVar>();
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	                a.add(ExprVar.make(null, "p" + i));
	                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	                a.clear();
	            }
	            
	           	Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.getFullyQualName())); //t.enabledAfterStep_transName
	            Expr genEventT = (DashOptions.isElectrum) ? tFuncCall : ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
	            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
	            Expr ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "genEvents"), sPrimeGenEventT);
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            	ssPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), ssPrimeGenEventT);
	            }
	            
	            Expr quant = (trans.getParentConcState().getIdentifiers().size() == 0) ? DashHelper.createUnaryExpr(ExprUnary.Op.NOT, ssPrimeGenEventT) : ExprQt.Op.NO.make(null, null, decls, ssPrimeGenEventT);
	            expr = (expr == null) ? quant : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, quant) ; // no p: param | enabledAfterStep_transName[s, s_next, t, genEvents, p]\n
        	}
            expr = ExprUnary.Op.NOOP.make(null, expr); 
            addPredicateAST(module, "testIfNextStable", "s", "s_next", "t", "genEvents", expr);
        }
        eventSize2Trans.clear();
    }
    
    private Expr addOtherTestIfState(DashModule module, int key, Expr expr) {
    	Expr expression = expr;
        for (int otherKey : eventSize2Trans.keySet()) { 
        	if ((otherKey == key) || !eventSize2Trans.containsKey(otherKey)) continue;
        	for (DashTrans trans: eventSize2Trans.get(otherKey)) {
	            List<Decl> decls = new ArrayList<Decl>();
	            List<ExprVar> a = new ArrayList<ExprVar>();
	            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	                a.add(ExprVar.make(null, "p" + i));
	                decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	                a.clear();
	            }
	            
	           	Expr tFuncCall = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, "enabledAfterStep_" + trans.getFullyQualName())); //t.enabledAfterStep_transName
	            Expr genEventT = (DashOptions.isElectrum) ? tFuncCall : ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), tFuncCall); //genEvents.t.enabledAfterStep_transName
	            Expr sPrimeGenEventT = ExprBadJoin.make(null, null, ExprVar.make(null, "t"), genEventT);
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
        for (DashTrans trans : module.getTransitions().values()) {
            int totalIEsSize = trans.getParentConcState().getIdentifiers().size(); 
            List<Decl> decls = new ArrayList<Decl>();
            List<ExprVar> a = new ArrayList<ExprVar>();
            for (int i = 0; i < trans.getParentConcState().getIdentifiers().size(); i++) {
	            a.add(ExprVar.make(null, "p" + i));
	            decls.add(new Decl(null, null, null, null, a, mult(ExprVar.make(null, trans.getParentConcState().getIdentifiers().get(i))))); //p: param
	            a.clear();
            }
            Expr preTransCall = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar("pre_" + trans.getFullyQualName())); //s.pre_transName
            preTransCall = DashHelper.addParametersJoin(preTransCall, totalIEsSize);
            preTransCall = (totalIEsSize == 0) ? preTransCall : ExprQt.Op.SOME.make(null, null, decls, preTransCall); // some p: param | transName[s, s_next, p]
            expr = (expr == null) ? preTransCall : DashHelper.createBinaryExpr(expr, ExprBinary.Op.OR, preTransCall);
        }

        //No need to add this predicate if there are no transitions in the model
        if (module.getTransitions().keySet().size() > 0) {
            addPredicateAST(module, "isEnabled", "s", null, null, null, expr);
        }
    }

    /****************************************** EQUALS PREDICATE ***************************************/
    
    /*
     * This function creates an AST for the following predicate: pred equals[s, s_next:
     * Snapshot] {}
     */
    private void createEqualsAST(DashModule module) {
        Expr expr = null;
        
        for (int i: module.getConfLevels()) {
        	Expr sNextConf = DashOptions.isElectrum ? DashHelper.sConfPrimed(i) : DashHelper.sNextConf(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextConf, ExprBinary.Op.EQUALS, DashHelper.sConf(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        for (int i: module.getConfLevels()) {
        	Expr sNextTaken = DashOptions.isElectrum ? DashHelper.sTakenPrimed(i) : DashHelper.sNextTaken(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextTaken, ExprBinary.Op.EQUALS, DashHelper.sTaken(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        for (int i: module.getEventLevels()) {
        	Expr sNextEvents = DashOptions.isElectrum ? DashHelper.sEventsPrimed(i) : DashHelper.sNextEvents(i);
        	Expr equals = DashHelper.createBinaryExpr(sNextEvents, ExprBinary.Op.EQUALS, DashHelper.sEvents(i));
        	expr = (expr == null) ? equals : DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
        }
        
        Expr sNextStable = DashOptions.isElectrum ? DashHelper.sStablePrimed() : DashHelper.sNextStable();
        Expr stableEquals = DashHelper.createBinaryExpr(sNextStable, ExprBinary.Op.EQUALS, DashHelper.sStable());
        expr = (module.getAllConcurrentStates ().size() > 1) ? DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, stableEquals) : expr;
        
        /* Conjunction of any env variables in the model 
        for(String concStateName: module.getEnvironmentalVarNames().keySet()) {
        	for(String envVar: module.getEnvironmentalVarNames().get(concStateName)) {
        		Expr fullyQualName = DashHelper.createExprVar(concStateName + "_" + envVar);
        		Expr sNextVar = DashOptions.isElectrum ? DashHelper.sVarPrimed(fullyQualName) : DashHelper.sNextVar(fullyQualName);
        		Expr equals = ExprBinary.Op.EQUALS.make(null, null, sNextVar, DashHelper.sVar(fullyQualName));
        		expr = ExprBinary.Op.AND.make(null, null, expr, equals);
        	}
        }*/
  
        for (String key : module.getRawVarNames().keySet()) {
            for (String var : module.getRawVarNames().get(key)) {
            	Expr fullyQualVarName = DashHelper.createExprVar(key + "_" + var);
            	Expr sNextVar = DashOptions.isElectrum ? DashHelper.sVarPrimed(fullyQualVarName) : DashHelper.sNextVar(fullyQualVarName);
            	Expr equals = DashHelper.createBinaryExpr(sNextVar, ExprBinary.Op.EQUALS, DashHelper.sVar(fullyQualVarName));
            	expr = DashHelper.createBinaryExpr(expr, ExprBinary.Op.AND, equals);
            }
        }       

        expr = ExprUnary.Op.NOOP.make(null, expr);
        addPredicateAST(module, "equals", "s", "s_next", null, null, expr);
    } 
 
    /****************************************** INIT PREDICATE ***************************************/
    
    /* This function creates the AST for the init conditions */
    private void createInitAST(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Map <Integer, ArrayList<Expr>> confToStates = new LinkedHashMap<Integer, ArrayList<Expr>>();
       
        ExprVar snapshot = ExprVar.make(null, "Snapshot");
        ExprVar p = ExprVar.make(null, "p");
        a.add(p);

        ExprVar s = ExprVar.make(null, "s");
        ExprVar stable = ExprVar.make(null, "stable");
        Expr expression = null;
        isCreatingInit = true;

        for (int key: module.getInitDefaultStates().keySet()) {
        	for (DashState state: module.getInitDefaultStates().get(key)) {
        		DashConcState parent = DashHelper.getParentConcState(state);
        		// ONLY CONSIDERED IF THE TOP LEVEL CONC STATE HAS NO BASIC STATES
        		if (parent == null) {
        			confToStates.put(key, new ArrayList<Expr>());
	    			confToStates.get(key).add(DashHelper.createParameterizedExpr(state.getRawName(), module.getAllConcurrentStates().get(state.getRawName())));
	    			continue;
        		}
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
        	Expr sConf = ExprBadJoin.make(null, null, s, ExprVar.make(null, "conf" + key));
        	Expr right = null;
        	for (Expr expr: confToStates.get(key)) {
        		right = (right == null) ? expr : DashHelper.createBinaryExpr(right, ExprBinary.Op.PLUS, expr);
        	}
    		sConf = DashHelper.createBinaryExpr(sConf, ExprBinary.Op.EQUALS, right);
    		expression = (expression == null) ? sConf : DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, sConf);
        }
        
        for (int key: confToStates.keySet()) {
        	Expr noSTaken = DashHelper.createUnaryExpr(ExprUnary.Op.NO, DashHelper.createExprBadJoin("s", "taken" + key));
    		expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, noSTaken);
        }
        
        if (module.hasEnvEvents()) {
            for (int key: module.getEventLevels()) {
                Expr binary = DashHelper.createBinaryExpr(DashHelper.sEvents(key), ExprBinary.Op.INTERSECT, DashHelper.addIdentifiersArrow(DashHelper.intEvent(), key)); // s.events & InternalEvents
                Expr unary = ExprUnary.Op.NO.make(null, binary); //no s.events & InternalEvent
                expression = ExprBinary.Op.AND.make(null, null, expression, unary);
            }
        } 
        
        if(module.hasHierarchy()) {
        	Expr sStableTrue = ExprBinary.Op.EQUALS.make(null, null, ExprBadJoin.make(null, null, s, stable), ExprVar.make(null, "True")); //s.stable = True
        	expression = ExprBinary.Op.AND.make(null, null, expression, sStableTrue);
        }
 
        for (DashInit init : module.getInitConditions()) {
            for (Expr expr : init.getAllExpressions()) {
                Expr modifiedExpr = getVarFromParentExpr(expr, init.getParentConcState(), module);
                expression = ExprBinary.Op.AND.make(null, null, expression, modifiedExpr);
            }
        }
        
        a.clear();
        decls.clear();
        a.add(s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //[s: Snapshot]
        a.clear();
        for (int i = 0; i < module.getIdentifierElements().size(); i++) {
        	a.add((ExprVar) DashHelper.createExprVar("p" + i));
            decls.add(new Decl(null, null, null, null, a, DashHelper.createExprVar(module.getIdentifierElements().get(i)))); //[p0: IE0]
            a.clear();
        }
        isCreatingInit = false;
        expression = ExprUnary.Op.NOOP.make(null, expression);
        module.addFunc(null, null, "init", null, decls, null, expression);
    }

    /************************************ HELPER FUNCTION FOR CREATING PREDICATES *****************************************/
    
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
    
    /* Add a new predicate to the Dash Module */
    void addPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        if (arg1 != null)
            a.add(ExprVar.make(null, arg1));
        if (arg2 != null && !DashOptions.isElectrum)
            a.add(ExprVar.make(null, arg2));
        if (arg3 != null)
            a.add(ExprVar.make(null, arg3));
        if (arg4 != null)
            a.add(ExprVar.make(null, arg4));
        
        if (a.size() > 0 && a.size() <= 2) { //Cannot add declarations if the predicate for no arguments
            decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        }
        else if (a.size() == 3) { //Only for EnabledAfterNextStep/testIfNextStable Predicate AST creation without EventLabel in the model
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1))), mult(snapshot)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
        	}
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }
        else if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1))), mult(snapshot)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
        	}
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), mult(ExprUnary.Op.SETOF.make(null, ExprVar.make(null, "InternalEvent")))));
        }
        
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    void addPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, int eventIes, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        if (arg1 != null)
            a.add(ExprVar.make(null, arg1));
        if (arg2 != null & !DashOptions.isElectrum) 
            a.add(ExprVar.make(null, arg2));
        if (arg3 != null)
            a.add(ExprVar.make(null, arg3));
        if (arg4 != null)
            a.add(ExprVar.make(null, arg4));

        if (a.size() > 0 && a.size() <= 2) { //Cannot add declarations if the predicate for no arguments
            decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        }
        else if (a.size() == 3) { //Only for EnabledAfterNextStep/testIfNextStable Predicate AST creation without EventLabel in the model
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1))), mult(snapshot)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
        	}
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
        }
        else if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
        	if (DashOptions.isElectrum) {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1))), mult(snapshot)));
        	}
        	else {
        		decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
        	}
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
        }
        
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /* Add a new Parameterized predicate to the Dash Module */
    private void addParameterizedPredicateAST(DashModule module, String predName, String arg1, String arg2, String arg3, String arg4, List<String> ies, int eventIes, Expr expression) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        if (arg1 != null)
            a.add(ExprVar.make(null, arg1));
        if (arg2 != null && !DashOptions.isElectrum)
            a.add(ExprVar.make(null, arg2));
        if (arg3 != null)
            a.add(ExprVar.make(null, arg3));
        if (arg4 != null)
            a.add(ExprVar.make(null, arg4));
        
        
        if (a.size() > 0 && a.size() <= 2) //Cannot add declarations if the predicate for no arguments
            decls.add(new Decl(null, null, null, null, a, mult(snapshot)));
        if (a.size() == 3 && DashOptions.isElectrum) { //Only for EnabledAfterNextStep Predicate AST creation
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "s"))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
        }
        if (a.size() == 4) { //Only for EnabledAfterNextStep Predicate AST creation
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg1), ExprVar.make(null, arg2))), mult(snapshot)));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg3))), ExprVar.make(null, "TransitionLabel")));
            decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, arg4))), DashHelper.addIdentifiersArrow(DashHelper.intEvent(), eventIes)));
        }
        
        for (int i = 0; i < ies.size(); i++) {
        	decls.add(new Decl(null, null, null, null, new ArrayList<ExprVar>(Arrays.asList(ExprVar.make(null, "p" + i))), ExprVar.make(null, ies.get(i)))); 
        }
        
        module.addFunc(null, null, predName, null, decls, null, expression);
    }
    
    /****************************************** DIFFERENT ATOMS FACT ***************************************/
    
    void createDifferentAtomsFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr sPrime = ExprVar.make(null, "s_next");
        a.add((ExprVar) s);
        a.add((ExprVar) sPrime);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        
        Expr equalsCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "equals"));//s.small_step
        equalsCall = ExprBadJoin.make(null, null, sPrime, equalsCall); //s_next.s.small_step
        Expr rightQT = ExprBinary.Op.IMPLIES.make(null, null, equalsCall, ExprBinary.Op.EQUALS.make(null, null, s, sPrime));
        Expr expr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s, s_next: Snapshot | equals[s, s_next] => s = s_next
    	
        module.addFact(null, "different_atoms", expr);
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
    
    /****************************************** REACHABILITY FACT ***************************************/
    
    void createReachabilityFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr s = ExprVar.make(null, "s");
        Expr reachabilityAxiomExpr = null; //This is the Reachability Axiom, all s : Snapshot | s in S .((Step.initial) <: * (Step.next_step) )
        
        Expr next = null;
        Expr initFirst = null;
        if (DashOptions.generateTraces) {
        	next = ExprVar.make(null, "snapshot/next"); //next
        	initFirst = ExprVar.make(null, "snapshot/first"); // ordering/first
        }
        else if(DashOptions.ctlModelChecking) {
        	next = ExprVar.make(null, "path_ctl/ks_sigma"); //next
        	initFirst = ExprVar.make(null, "path_ctl/ks_s0"); // ordering/first
        }
        else {
        	ExprVar sInit = ExprVar.make(null, "s_init");
        	Expr initSInit = ExprBadJoin.make(null, null, sInit, ExprVar.make(null, "init")); //s_init.init or init[s_init]
        	next = ExprBinary.Op.JOIN.make(null, null, snapshot, ExprVar.make(null, "next")); //Snapshot.next
        	Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (Snapshot.next)
        	Expr domain = ExprBinary.Op.DOMAIN.make(null, null, sInit, reflexiveClosure); // (s_init <: * (next))
        	Expr joinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot.(s_init <: * (next))
        	Expr sInDomain = ExprBinary.Op.IN.make(null, null, s, joinDomain); // s in Snapshot.(s_init <: * (next))
        	Expr sInitAndSInDomain = ExprBinary.Op.AND.make(null, null, initSInit, sInDomain); // init[s_init] and s in (s_init <: * (next))
        	a.add(sInit);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s_init: Snapshot
        	Expr someQt = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), sInitAndSInDomain); // some s: Snapshot | init[s_init] and s in (s_init <: * (next))
        	a.clear();
        	decls.clear();
        	a.add((ExprVar) s);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        	Expr reachabilityAxiom = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), someQt); // all s: Snapshot | some s_init: Snapshot | init[s_init] and s in (s_init <: * (next))
        	addPredicateAST(module, "reachabilityAxiom", null, null, null, null, reachabilityAxiom);
        	return;
        }
     
        Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (next)
        Expr domain = ExprBinary.Op.DOMAIN.make(null, null, initFirst, reflexiveClosure); // (ordering/first <: * (next))
        
        Expr SJoinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot. (ordering/first <: * (next))
        Expr sInSJoinDomain = ExprBinary.Op.IN.make(null, null, s, SJoinDomain); // s in Snapshot. (ordering/first <: * (next))
        
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        reachabilityAxiomExpr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), sInSJoinDomain); // all s: Snapshot | s in Snapshot. ((Step.initial) <: * (Step.next_step) )
        module.addFact(null, "reachabilityFact", reachabilityAxiomExpr);
    }
    
    /****************************************** TRACES FACT ***************************************/
    
    void createTracesFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        a.add((ExprVar) s);
        
    	Expr expression = createInitCall(module, true); // init[first]
    	
    	Expr smallStep = DashHelper.createExprBadJoin(DashHelper.s(), "small_step");  //ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step")); //small_step[s]
    	Expr sNext = DashHelper.createBinaryExpr(DashHelper.s(), ExprBinary.Op.JOIN, DashHelper.createExprVar("next")); //s.next
    	smallStep = ExprBadJoin.make(null, null, sNext, smallStep); // small_step[s, s.next]
    	Expr notSinLast = ExprUnary.Op.NOT.make(null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "snapshot/last"))); // !(s in last)
    	Expr implies = ExprBinary.Op.IMPLIES.make(null, null, notSinLast, smallStep); // !(s in last) => small_step[s, s.next]
    	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
    	Expr smallStepQuant = ExprQt.Op.ALL.make(null, null, decls, implies); // all s: Snapshot | !(s in last) => small_step[s, s.next]
    	
    	Expr notSmallStep = ExprUnary.Op.NOT.make(null, smallStep); // !small_step[s, s.next]
    	Expr equals = DashHelper.createExprBadJoin(DashHelper.s(), "equals"); // equals[s]
    	equals = ExprBadJoin.make(null, null, sNext, equals); // equals[s, s.next]
    	Expr impliesEquals = DashHelper.createBinaryExpr(notSinLast, ExprBinary.Op.AND, notSmallStep);
    	impliesEquals = ExprBinary.Op.IMPLIES.make(null, null, impliesEquals, equals);
    	impliesEquals = ExprQt.Op.ALL.make(null, null, decls, impliesEquals);
    	
    	expression = ExprBinary.Op.AND.make(null, null, expression, smallStepQuant);
    	expression = ExprBinary.Op.AND.make(null, null, expression, impliesEquals);
    	decls.clear();
    	
        Expr iffLeft = ExprUnary.Op.NOT.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "stable"))); // ! stable[s] or s.stable = False
        Expr iffRight = ExprUnary.Op.SOME.make(null, ExprBadJoin.make(null, null, s, ExprVar.make(null, "snapshot/next")));
        Expr iffExpr = ExprBinary.Op.IMPLIES.make(null, null, iffLeft, iffRight);
    	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr quant = ExprQt.Op.ALL.make(null, null, decls, iffExpr); // all s: Snapshot | !stable[s] => some s.nextStep
        a.clear();
        decls.clear(); 
        
        if (module.hasHierarchy())
        	expression = ExprBinary.Op.AND.make(null, null, expression, quant);
        	
        module.addFact(null, "traces", expression);
    }
    
    void createElectrumTracesFact(DashModule module) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot = ExprVar.make(null, "Snapshot");
        ExprVar s = ExprVar.make(null, "s");
        a.add(s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot 
        
    	Expr expression = createInitCall(module, true); // init[first]
    	expression = ExprQt.Op.ONE.make(null, null, decls, expression);

    	Expr smallStep = DashHelper.createExprBadJoin(s, "small_step"); //small_step[s]
    	Expr alwaysSmallStep = ExprQt.Op.ALL.make(null, null, decls, smallStep);
    	alwaysSmallStep = DashHelper.createUnaryExpr(ExprUnary.Op.ALWAYS, alwaysSmallStep);
    	
    	expression = DashHelper.createBinaryExpr(expression, ExprBinary.Op.AND, alwaysSmallStep);
  
        module.addFact(null, "traces", expression);
    }
    
    Expr createInitCall(DashModule module, boolean isTraces) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        for (int i = 0; i < module.getIdentifierElements().size(); i++) {
        	a.add(ExprVar.make(null, "p" + i));
        	decls.add(new Decl(null, null, null, null, a, ExprVar.make(null, module.getIdentifierElements().get(i)))); //p0: PID...
        	a.clear();
        }
        
        Expr initCall = isTraces ? DashHelper.createExprBadJoin(DashHelper.createExprVar("snapshot/first"), DashHelper.createExprVar("init")) : DashHelper.createExprBadJoin(DashHelper.createExprVar("s"), DashHelper.createExprVar("init"));
        initCall = DashOptions.isElectrum ? DashHelper.createExprBadJoin(DashHelper.createExprVar("s"), DashHelper.createExprVar("init")) : initCall;
        initCall = DashHelper.addParametersJoin(initCall, module.getIdentifierElements().size());
        Expr quant = (module.getIdentifierElements().size() == 0) ? initCall : ExprQt.Op.ALL.make(null, null, decls, initCall);
        
    	return quant;
    }
    
    
    /*************************** CTL MODULE FACT FUNCION ******************************/
    
    void createCTLFact(DashModule module) {
    	// Creating the following expression:     
        //	all s, s_next | small_step[s, s_next] => s->s_next = ks_sigma
        //	Step.initial = ks_s0
    	
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        ExprVar s = ExprVar.make(null, "s");
        ExprVar sNext = ExprVar.make(null, "s_next");
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr expression = null; //This is the final expression to be stored in the Fact AST
        a.add(s);
        a.add(sNext);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s, s_next: Snapshot 
        
        Expr smallStepCall = ExprBadJoin.make(null, null, s, ExprVar.make(null, "small_step"));//s_next.small_step
        smallStepCall = ExprBadJoin.make(null, null, sNext, smallStepCall); //s.s_next.small_step
        Expr arrow = ExprBinary.Op.ARROW.make(null, null, s, sNext); // s->s_next
        Expr sSNextInSigma = ExprBinary.Op.IN.make(null, null, arrow, ExprVar.make(null, "ks_sigma")); // s->s_next = ks_sigma
        Expr implesEqualsSigma = ExprBinary.Op.IFF.make(null, null, sSNextInSigma, smallStepCall); // ->s_next = ks_sigma iff small_step[s, s_next]
        expression = ExprQt.Op.ALL.make(null, null, decls, implesEqualsSigma);
        a.clear();
        decls.clear();
        
        /*
         * Creating the following expression: all s: Snapshot | s in ks_s0 iff init[s]
         */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        Expr initCall = createInitCall(module, false);
        Expr rightQT = ExprBinary.Op.IFF.make(null, null, ExprBinary.Op.IN.make(null, null, s, ExprVar.make(null, "ks_s0")), initCall);
        expression = ExprBinary.Op.AND.make(null, null, ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT), expression); //all s: Snapshot | s in ks_s0 iff init[s]
        a.clear();
        decls.clear();
        
        module.addFact(null, "tcmc", expression);
    }
    
    /*************************************** KEEPING VARIABLES UNCHANGED ***************************************/
   
    //Find the variables that are unchanged during a transition
    Map<String, DashConcState> getUnchangedVars(List<Expr> exprList, DashModule module) {
    	Map<String, DashConcState> unchangedVariables = new LinkedHashMap<String, DashConcState>(module.getVariableConcState());
      
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
        	param = (i == 0) ? DashHelper.createBinaryExpr(param, ExprBinary.Op.MINUS, DashHelper.createExprVar("p" + i)) : param;
            a.add(ExprVar.make(null, "ie" + i));
            decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
            a.clear();
        }    
        
        //Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); 
        Expr binaryLeft = DashOptions.isElectrum ? DashHelper.sVarPrimed(var) : DashHelper.createExprBadJoin(DashHelper.sNext(), DashHelper.createExprVar(var));
        for (int i = 0; i < varParent.getIdentifiers().size(); i++) {
        	binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryLeft); 
        }
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //quant.(s_next).var
        for (int i = 0; i < varParent.getIdentifiers().size(); i++) {
        	binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryRight); 
        }
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        
        if (varParent.getIdentifiers().size() > 1) {
        	List<String> identifiers = new ArrayList<String>(varParent.getIdentifiers());
        	identifiers.remove(0);
        	binaryEquals = constrainLocallyChangedNestedVar(binaryEquals, var, varParent, identifiers);
        }
        
        return (varParent.getIdentifiers().size() == 0) ? binaryEquals : ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
    }
    
    private Expr constrainLocallyChangedNestedVar(Expr equals, String var, DashConcState parent, List<String> identifiers) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        for (int i = 0; i < identifiers.size() ; i++) {
        	Expr param = ExprVar.make(null, identifiers.get(i));
        	param = (i == 0) ? DashHelper.createBinaryExpr(param, ExprBinary.Op.MINUS, DashHelper.createExprVar("p" + identifiers.size())) : param;
            a.add(ExprVar.make(null, "ie" + i));
            decls.add(new Decl(null, null, null, null, a, mult(param))); //p: param
            a.clear();
        }
      
        //Expr binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "s_next"), ExprVar.make(null, var)); 
        Expr binaryLeft = DashOptions.isElectrum ? DashHelper.sVarPrimed(var) : DashHelper.createExprBadJoin(DashHelper.sNext(), DashHelper.createExprVar(var));
        binaryLeft = DashHelper.addParametersJoin(binaryLeft, parent.getIdentifiers().size() - identifiers.size());
        for (int i = 0; i < identifiers.size(); i++) {
        	binaryLeft = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryLeft); 
        }
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //quant.(s_next).var
        binaryRight = DashHelper.addParametersJoin(binaryRight, parent.getIdentifiers().size() - identifiers.size());
        for (int i = 0; i < identifiers.size(); i++) {
        	binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "ie" + i), binaryRight); 
        }
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);
        binaryEquals = ExprQt.Op.ALL.make(null, null, decls, binaryEquals);
        binaryEquals = DashHelper.createBinaryExpr(equals, ExprBinary.Op.AND, binaryEquals);
        
        if (identifiers.size() > 1) {  
        	identifiers.remove(0);
        	binaryEquals = constrainLocallyChangedNestedVar(binaryEquals, var, parent, identifiers);
        }
        
        return binaryEquals;
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
    	Expr binaryLeft = DashOptions.isElectrum ? DashHelper.sVarPrimed(var) : DashHelper.createExprBadJoin(DashHelper.sNext(), DashHelper.createExprVar(var));
        Expr binaryRight = ExprBadJoin.make(null, null, ExprVar.make(null, "s"), ExprVar.make(null, var)); //s_next.variableParent_varName
        Expr binaryEquals = ExprBinary.Op.EQUALS.make(null, null, binaryLeft, binaryRight);

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
        	Expr sNextJoinBuffer = DashOptions.isElectrum ? DashHelper.sVarPrimed(bufferName) : DashHelper.sNextVar(bufferName); //s_next.bufferName
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
    	DashConcState parentConcState = parent;
    	
        Expr expression = expr; 
        
        /* If the var refers to a parameterizerd concurrent process, return 'p' as this refers to the current process */
        if(expression.toString().equals("this")) {
        	return isCreatingInit && parent.isParameterized() ? ExprVar.make(null, "p" + module.getIdentifierElements().indexOf(parent.getReplicatedIdentifier())) : 
        		ExprVar.make(null, "p0");
        }
    	
        List<String> variablesInParent = module.getRawVarNames().getOrDefault(parentConcState.getFullyQualName(), new ArrayList<>());
        List<String> envVariablesInParent = module.getEnvironmentalVarNames().getOrDefault(parentConcState.getFullyQualName(), new ArrayList<>());

        //If we make a reference to a conc state outside of the current conc state, find it and 
        //modify the value of the expression accordingly
    	if(expr.toString().contains("/")) {
    		String expressionStr = expr.toString();
    		Optional<DashSuperState> variableParent = DashHelper.findVariableParent(module, parent, expressionStr);
    		if (variableParent.isPresent()) {
    			// Get the AND state in which the variable is located (if it is located in an OR state, then we 
    			// get the parent AND state of the OR state
    			parentConcState = (variableParent.get() instanceof DashConcState) ? (DashConcState) variableParent.get() : variableParent.get().getParentConcState();
    			// Get the name of the variable (ANDState/ORState/var) -> var
    			String variable = expressionStr.substring(expressionStr.lastIndexOf('/') + 1);
    			Expr exprVar = DashHelper.createExprVar(variable);
    			// Get all the variables
    			variablesInParent = module.getRawVarNames().getOrDefault(parentConcState.getFullyQualName(), new ArrayList<>());
    	        envVariablesInParent = module.getEnvironmentalVarNames().getOrDefault(parentConcState.getFullyQualName(), new ArrayList<>());
    	        expression = modifyVar(module, expression, parentConcState, variableParent.get(), exprVar, variablesInParent, false, true);
    	        expression = modifyVar(module, expression, parentConcState, variableParent.get(), exprVar, envVariablesInParent, false, true);
    			return expression;
    		} else {
    	        expression = modifyVar(module, expression, parentConcState, parentConcState, expr, variablesInParent, false, true);
    	        expression = modifyVar(module, expression, parentConcState, parentConcState, expr, envVariablesInParent, false, true);
    			return expression;
    		}
    	}
        
        if (variablesInParent != null)
            expression = modifyVar(module, expression, parentConcState, parentConcState, expr, variablesInParent, false, isRef);
        if (envVariablesInParent != null)
            expression = modifyVar(module, expression, parentConcState, parentConcState, expr, envVariablesInParent, true, isRef);
        
        // Look for the variable in nested AND-states
        for (DashConcState innerConcState: DashHelper.getNestedConcStates(parentConcState)) {
            if (module.getRawVarNames().get(innerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, innerConcState, innerConcState, expr, module.getRawVarNames().get(innerConcState.getFullyQualName()), false, isRef);
            if (module.getEnvironmentalVarNames().get(innerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, innerConcState, innerConcState, expr, module.getEnvironmentalVarNames().get(innerConcState.getFullyQualName()), true, isRef);
        }

        // Look for the variable in parent AND-states
        DashConcState outerConcState = DashHelper.getTopLevelConcStates(parentConcState);
        while (outerConcState != null) {
            if (module.getRawVarNames().get(outerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, outerConcState, outerConcState, expr, module.getRawVarNames().get(outerConcState.getFullyQualName()), false, isRef);
            if (module.getEnvironmentalVarNames().get(outerConcState.getFullyQualName()) != null)
                expression = modifyVar(module, expression, outerConcState, outerConcState, expr, module.getEnvironmentalVarNames().get(outerConcState.getFullyQualName()), true, isRef);
            outerConcState = outerConcState.getParentConcState();
        }
        
        expression = replaceWithActionExpr(expression, parentConcState, module);
        expression = replaceWithConditionExpr(expression, parentConcState, module);
        
        return expression;
    }
        
    private Expr modifyVar(DashModule module, Expr expression, DashConcState parent, DashSuperState immediateParent, Expr expr, List<String> varsInParent, boolean isEnvVar, boolean isRef) {
        for (String var : varsInParent) {
        	var = var.replace('/', '_');
        	expr = DashHelper.createExprVar(expr.toString().replace('/', '_'));
        	expr = (immediateParent instanceof DashState) ? DashHelper.createExprVar(DashHelper.calculateStateNameWithoutConcState((DashState) immediateParent) + expr.toString()) : expr; 
        	String qualifiedVarName = parent.getFullyQualName() + '_' + var;
            if (expr.toString().equals(var + "'")) {
            	changedVars.put(qualifiedVarName, parent);
            	if (!isRef) {
            		changedLocalVars.put(qualifiedVarName, parent);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);
            		Expr sNextVar = DashHelper.createBinaryExpr(DashHelper.sNext(), ExprBinary.Op.JOIN, variable);
            		sNextVar = DashHelper.addParametersJoin(sNextVar, parent.getIdentifiers().size());
            		return sNextVar;
            	}
            	else {
            		changedRefVars.add(qualifiedVarName);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);         	
            		Expr sNextVar = DashOptions.isElectrum ? DashHelper.sVarPrimed(variable) : DashHelper.createBinaryExpr(DashHelper.sNext(), ExprBinary.Op.JOIN, variable);
            		sNextVar = parent.getIdentifiers() != null ? DashHelper.addParametersJoin(sNextVar, parent.getIdentifiers().size() - 1) : sNextVar; // For nested replicated components within replicated components
            		return sNextVar;
            	}
            }
            else if (expr.toString().equals(var)) {
            	if (isCreatingEnabledAfterPred && isEnvVar) {
            		return DashHelper.createExprBadJoin(DashHelper._s(), qualifiedVarName);
            	}
            	else if (isCreatingEnabledAfterPred && DashOptions.isElectrum && !isRef) {
        			Expr variable = DashHelper.createExprVar(qualifiedVarName);
        			Expr sVarPrimed = DashHelper.sVarPrimed(variable);
        			sVarPrimed = DashHelper.addParametersJoin(sVarPrimed, parent.getIdentifiers().size());
        			return sVarPrimed;
            	}
             	else {
            		if (!isRef && (isCreatingInit) && (!isCreatingExprQt) && parent.getIdentifiers().size() > 0) {
            			Expr variable = DashHelper.createExprVar(qualifiedVarName);
	                	Expr sVar =  DashHelper.createBinaryExpr(DashHelper.s(), ExprBinary.Op.JOIN, variable);
	                	Expr idSVar = DashHelper.createBinaryExpr(DashHelper.createExprVar("p" + module.getIdentifierElements().indexOf(parent.getReplicatedIdentifier())), ExprBinary.Op.JOIN, sVar); //DashHelper.addParametersJoin(sVar, parent.getIdentifiers().size());;
	                	return idSVar;
            		}
            		else if (!isRef && !(isCreatingInit && isCreatingExprQt)) { // No need to DotJoin the "p0" expr if it is a reference to another parameterized concurrent state
            			Expr variable = DashHelper.createExprVar(qualifiedVarName);
	                	Expr sVar =  DashHelper.createBinaryExpr(DashHelper.s(), ExprBinary.Op.JOIN, variable);
	                	sVar= DashHelper.addParametersJoin(sVar, parent.getIdentifiers().size());
	                	return sVar;
                	}
                	else {
                		Expr sVar = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar(qualifiedVarName));
                		Expr p0SVar = parent.getIdentifiers() != null ? DashHelper.addParametersJoin(sVar, parent.getIdentifiers().size() - 1) : sVar; // For nested replicated components within replicated components
                		return p0SVar;
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
        	 foundBuffer = (bufferCommands.contains(right.toString()) && module.getBuffers().containsKey(joinLeftRightRight.toString())) ? true : false;
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprVar)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
            	 //System.out.println("Join Left: " + joinLeft + " joinLeftRight: " + joinLeftRight);
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing1: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 paramBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 } 
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: (p.bufferName).remove [a buffer call with no parameters such as remove]
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBinary && joinLeft.left instanceof ExprVar)) {
        		 ExprBinary joinLeftRight = (ExprBinary) joinLeft.right;
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("ChangingBuffer2: " + joinLeftRight.right.toString() + " Left: " + joinLeft + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 changedLocalVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: ConcState[buffer1.first]/buffer0.add[pid]
        	 if (bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprBadJoin)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing3: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
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

    
    /*************************** SINGLE STEP FACT FUNCTION ******************************/
    
    /* Create the single input assumption */
    void createSingleStepFact(DashModule module)
    {
        // Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent)
    	
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprUnary.Op.ONE.make(null, ExprVar.make(null, "Snapshot"));
        Expr s = ExprVar.make(null, "s");
        Expr expression = null; //This is the final expression to be stored in the Fact AST
        
        /* Creating the following expression: lone (s.events & EnvironmentEvent) */
        Expr rightQT = null;
        Expr join = ExprBadJoin.make(null, null, s, ExprVar.make(null, "events")); // s.events
        Expr rightBinary = ExprBinary.Op.INTERSECT.make(null, null, join, ExprVar.make(null, "EnvironmentEvent")); // s_next.events & InternalEvent
        rightQT = ExprUnary.Op.LONE.make(null, rightBinary); // no (s_next.events & InternalEvent)
        
        /* Creating the following expression: all s: Snapshot | lone (s.events & EnvironmentEvent) */
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        expression = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), rightQT); //all s: Snapshot | lone (s.events & EnvironmentEvent)
        
        module.addFact(null, "", expression);
    }
    
    /*************************** SIGNIFICANCE AXIOM FUNCIONS ******************************/
    
    void createSignificanceAxiomAST(DashModule module)
    {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        
        Expr snapshot = ExprVar.make(null, "Snapshot");
        Expr s = ExprVar.make(null, "s");
        Expr reachabilityAxiomExpr = null; //This is the Reachability Axiom, all s : Snapshot | s in S .((Step.initial) <: * (Step.next_step) )
        
        Expr next = null;
        Expr initFirst = null;
        if (DashOptions.generateTraces) {
        	next = ExprVar.make(null, "snapshot/next"); //next
        	initFirst = ExprVar.make(null, "snapshot/first"); // ordering/first
        }
        else if(DashOptions.ctlModelChecking) {
        	next = ExprVar.make(null, "path_ctl/ks_sigma"); //next
        	initFirst = ExprVar.make(null, "path_ctl/ks_s0"); // ordering/first
        }
        else {
        	ExprVar sInit = ExprVar.make(null, "s_init");
        	Expr initSInit = ExprBadJoin.make(null, null, sInit, ExprVar.make(null, "init")); //s_init.init or init[s_init]
        	next = ExprBinary.Op.JOIN.make(null, null, snapshot, ExprVar.make(null, "next")); //Snapshot.next
        	Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (Snapshot.next)
        	Expr domain = ExprBinary.Op.DOMAIN.make(null, null, sInit, reflexiveClosure); // (s_init <: * (next))
        	Expr joinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot.(s_init <: * (next))
        	Expr sInDomain = ExprBinary.Op.IN.make(null, null, s, joinDomain); // s in Snapshot.(s_init <: * (next))
        	Expr sInitAndSInDomain = ExprBinary.Op.AND.make(null, null, initSInit, sInDomain); // init[s_init] and s in (s_init <: * (next))
        	a.add(sInit);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s_init: Snapshot
        	Expr someQt = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), sInitAndSInDomain); // some s: Snapshot | init[s_init] and s in (s_init <: * (next))
        	a.clear();
        	decls.clear();
        	a.add((ExprVar) s);
        	decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        	Expr reachabilityAxiom = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), someQt); // all s: Snapshot | some s_init: Snapshot | init[s_init] and s in (s_init <: * (next))
        	addPredicateAST(module, "reachabilityAxiom", null, null, null, null, reachabilityAxiom);
        	return;
        }
     
        Expr reflexiveClosure = ExprUnary.Op.RCLOSURE.make(null, next); // * (next)
        Expr domain = ExprBinary.Op.DOMAIN.make(null, null, initFirst, reflexiveClosure); // (ordering/first <: * (next))
        
        Expr SJoinDomain = ExprBadJoin.make(null, null, snapshot, domain); // Snapshot. (ordering/first <: * (next))
        Expr sInSJoinDomain = ExprBinary.Op.IN.make(null, null, s, SJoinDomain); // s in Snapshot. (ordering/first <: * (next))
        
        a.add((ExprVar) s);
        decls.add(new Decl(null, null, null, null, a, mult(snapshot))); //s: Snapshot
        reachabilityAxiomExpr = ExprQt.Op.ALL.make(null, null, new ArrayList<Decl>(decls), sInSJoinDomain); // all s: Snapshot | s in Snapshot. ((Step.initial) <: * (Step.next_step) )
        addPredicateAST(module, "reachabilityAxiom", null, null, null, null, reachabilityAxiomExpr);
    }
    
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
        for (String transName: module.getTransitions().keySet())
        {
        	Expr sJoinTrans = ExprBadJoin.make(null, null, s, ExprVar.make(null, transName)); //T[s] or s.T
        	Expr join = ExprBadJoin.make(null, null, sNext, sJoinTrans); // T[s, s_next] or s_next.s.T
        	Expr quantified = ExprQt.Op.SOME.make(null, null, new ArrayList<Decl>(decls), join); // some s, s_next: Snapshot | T[s, s_next]
        	
        	if (expression == null)
        		expression = quantified;
        	else
        		expression = ExprBinary.Op.AND.make(null, null, expression, quantified);
        }
        
        addPredicateAST(module, "operationsAxiom", null, null, null, null, expression);
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
    
    DashState getState(String stateName, DashModule module) {
    	return module.getORStates().get(stateName);
    }
    
    /* Get all the transitions declared within a concurrent state */
    private List<String> getTransitions(DashModule module, DashConcState concState)
    {
    	List<String> transitions = new ArrayList<String>();
    	for (DashTrans trans: module.getTransitions().values()) {
    		if (DashHelper.getParentConcState(trans.getParent()).getFullyQualName().equals(concState.getFullyQualName()))
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
    		if (state.getInnerORStates().size() == 0 && state.getInnerConcStates().size() == 0) {
    			i++;
    		}
    	}
    	return i;
    }
    
    /* Get all the events declared within a concurrent state */
    private List<String> getEvents(DashConcState concState)
    {
    	List<String> events = new ArrayList<String>();
    	for (DashEvent event: concState.getEvents()) {
    		events.add(event.getRawName());
    	}
    	return events;
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
    	DashState sourceState = getState(trans.getOrigin().getAllOrigins().get(0), module);
    	
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
    	for(DashState state: module.getORStates().values()) {
    		for(DashEnter enter: state.getEnters()) {
    			expr = getVarFromParentExpr(enter.getExpr(), DashHelper.getParentConcState(state.getParent()), module);
    			addPredicateAST(module, "enter_" + state.getFullyQualName(), "s", null, null, null, expr);
    		}
    	}
    }
    
    public void createExitPredAST(DashModule module) {
    	Expr expr = null;
    	for(DashState state: module.getORStates().values()) {
    		for(DashExit exit: state.getExits()) {
    			expr = getVarFromParentExpr(exit.getExpr(), DashHelper.getParentConcState(state.getParent()), module);
    			addPredicateAST(module, "exit_" + state.getFullyQualName(), "s", null, null, null, expr);
    		}
    	}
    }
    
    private Expr createExitAST(Expr expression, DashState sourceState, DashTrans transition) {
        if(transition.getOrigin().getAllOrigins().size() > 0 && sourceState != null) {        	
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
            for (DashAction value : module.getActions().values()) {
                if (expr.toString().equals(value.getRawName()))
                	return getVarFromParentExpr(value.getAction(), parent, module);
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
    	isCreatingInvariant = true;
    	for(DashInvariant invar: module.getInvariants().values()) {
    		addInvariantFact(invar, module);
    	}
    	isCreatingInvariant = false;
    } 

    private void addInvariantFact(DashInvariant invar, DashModule module) {
    	Expr expression = null;

    	for(Expr expr: invar.getAllExpressions()) {
    		if (expression == null)
    			expression = getVarFromParentExpr(expr, DashHelper.getParentConcState(invar.getParentConcState()), module);
    		else
    			expression = ExprBinary.Op.AND.make(null, null, getVarFromParentExpr(expr, DashHelper.getParentConcState(invar.getParentConcState()), module), expression);
        }

        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr snapshot =  ExprVar.make(null, "Snapshot");
        a.add(ExprVar.make(null, "s"));
        decls.add(new Decl(null, null, null, null, a, mult(snapshot)));

    	Expr quantifiedExpr = ExprQt.Op.ALL.make(null, null, decls, expression);

    	module.addFact(null, invar.getRawName(), quantifiedExpr);
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
    		if (module.getRawBufferToIndexSig().containsKey(scope.sig.label)) {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(module.getRawBufferToIndexSig().get(scope.sig.label), 
	        			AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);
    		}
    		else if (module.getBufferElemToConcState().containsKey(scope.sig.label)){
    			paramScope = scope.endingScope;
    			totalParamScope += paramScope;

	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, 
	        			AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);    			
    		} 
    		else {
	        	CommandScope sigNum = new CommandScope(null            , Sig.NONE, scope.isExact,          scope.endingScope, scope.endingScope,             1    );
	        	CommandScope sigScope = new CommandScope(null, new PrimSig(scope.sig.label, 
	        			AttrType.WHERE.make(new Pos(null, 0, 0))), sigNum.isExact, sigNum.startingScope, sigNum.endingScope, sigNum.increment);
	        	scopes.add(sigScope);  
    		}
    	}
    	
		for (DashConcState concState: module.getAllConcurrentStates().values()) {
			stateLabelScope += getBasicStateCount(getStates(concState));
			transitionLabelScope += getTransitions(module, concState).size();
		}
		
		CommandScope stateNumber = new CommandScope(null            , Sig.NONE, true,          stateLabelScope, stateLabelScope,             1    );
		CommandScope stateSigScope = new CommandScope(null, new PrimSig("StateLabel", 
				AttrType.WHERE.make(new Pos(null, 0, 0))), stateNumber.isExact, stateNumber.startingScope, stateNumber.endingScope, stateNumber.increment);
		scopes.add(stateSigScope);
		
		CommandScope transitionNumber = new CommandScope(null            , Sig.NONE, true,          transitionLabelScope, transitionLabelScope,             1    );
		CommandScope transitionSigScope = new CommandScope(null, new PrimSig("TransitionLabel", 
				AttrType.WHERE.make(new Pos(null, 0, 0))), transitionNumber.isExact, transitionNumber.startingScope, transitionNumber.endingScope, transitionNumber.increment);
		scopes.add(transitionSigScope);
        
        int eventLabelScope = 0;
        if(module.hasEnvEvents()) {
        	eventLabelScope = module.getEventConcState().size();
        }
        
		CommandScope number = new CommandScope(null            , Sig.NONE, true,          eventLabelScope, eventLabelScope,             1    );
		CommandScope sigScope = new CommandScope(null, new PrimSig("EventLabel", AttrType.WHERE.make(new Pos(null, 0, 0))), number.isExact, number.startingScope, number.endingScope, number.increment);
		scopes.add(sigScope);
		
		CommandScope identNumber = new CommandScope(null            , Sig.NONE, true,          totalParamScope, totalParamScope,             1    );
		CommandScope identifiersScope = new CommandScope(null, new PrimSig("Identifiers", 
				AttrType.WHERE.make(new Pos(null, 0, 0))), identNumber.isExact, identNumber.startingScope, identNumber.endingScope, identNumber.increment);
		scopes.add(identifiersScope);
		
		return command.check ? createCommand(false,ExprVar.make(null, "c"), null , ExprVar.make(null, command.label) ,null, scopes, null, module) 
				: createCommand(false,ExprVar.make(null, "r"), null , ExprVar.make(null, command.label) ,null, scopes, null, module);
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
}
