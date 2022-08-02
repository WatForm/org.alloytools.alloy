package ca.uwaterloo.watform.transform;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashFrom;
import ca.uwaterloo.watform.ast.DashGoto;
import ca.uwaterloo.watform.ast.DashOn;
import ca.uwaterloo.watform.ast.DashSend;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTemplateCall;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashTransTemplate;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import edu.mit.csail.sdg.ast.Decl;


import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashToCoreDash {

    int transitionCount;
    
    public DashToCoreDash() {
    	transitionCount = 0;
    }
    
    public DashModule transformToCoreDash(DashModule module, String fileName, String path) throws IOException {
    	DashModule coreDashModule = new DashModule(module, fileName, path, true);
        getAllTransitions(coreDashModule);
        modifyTransitions(coreDashModule);
        modifyGoToCommands(coreDashModule);   
        modifyFromCommands(coreDashModule);
        modifyTransitionParent(coreDashModule); 
        return coreDashModule;
    }

     private void modifyTransitions(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
            trans.setOrigin(new DashFrom(completeFromCommand(trans, module), false));
            trans.gotoExpr = completeGoToCommand(trans, module);
            trans.onExpr = completeOnCommand(trans, module);
            trans.sendExpr = completeSendCommand(trans, module);
            trans.doExpr = addAction(trans.doExpr, module);
            trans.whenExpr = addCondition(trans.whenExpr, module);
        }
    }
    
    /* Check the source state of a transition, and set that source state as its parent. Simplifies the 
     * CoreDash to Alloy AST conversion. Then add this transition to the list of transitions for that state */
     private void modifyTransitionParent(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
        	DashState sourceState = DashHelper.getState(trans.getOrigin().fromExpr.get(0).replace("/", "_"), module); 	
        	if(sourceState != null) {
        		trans.setParent(sourceState);
        		
        		for(DashState state: module.states.values()) {
        			if(state.getFullyQualName().equals(sourceState.getFullyQualName()))
        				state.addModifiedTransition(trans);
        		}
        	}     	
        }
    } 
    
    /* Check if a GoTo command transitions to a state that has inner OR states. If so,
     * then that transition will need to transition to the default inner OR state */
     private void modifyGoToCommands(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
        	DashState destinationState = DashHelper.getState(trans.gotoExpr.gotoExpr.get(0).replace("/", "_"), module);
        	String defaultInnerState = "";
        	/* destState is null if the destination state is a concurrent state (it has no OR states) */
        	if(destinationState != null && destinationState.getInnerConcStates().size() == 0) {
        		defaultInnerState = getDefaultState(destinationState);
        		trans.gotoExpr.gotoConcState = getParentConcState(destinationState);
        		trans.gotoExpr = trans.gotoExpr.param == null ? new DashGoto(new ArrayList<String>(Arrays.asList(defaultInnerState))) : new DashGoto(null, new ArrayList<String>(Arrays.asList(defaultInnerState)), trans.gotoExpr.param);
        	}
        	else if (destinationState != null && destinationState.getInnerConcStates().size() > 0) {
        		Map<String, DashConcState> defaultStates = new LinkedHashMap<String, DashConcState>();
        		for (DashConcState innerConcState: destinationState.getInnerConcStates()) {
        			Map<String, DashConcState> defaultState = new LinkedHashMap<String, DashConcState>(getDefaultStates(innerConcState, module, new LinkedHashMap<String, DashConcState>()));
        			for (String key: defaultState.keySet()) {
        				defaultStates.put(key, defaultState.get(key));
        			}
        		}
    			trans.gotoExpr.gotoExprs = new LinkedHashMap<String, DashConcState>(defaultStates);
    			trans.gotoExpr.enteringDefaultStates = true;
        	}   
        }
    }
    
    /* Check if leave a state will result in other concurrent states leaving their current state */
     private void modifyFromCommands(DashModule module) {
        for (DashTrans trans : module.transitions.values()) {
        	DashState fromState = DashHelper.getState(trans.getOrigin().fromExpr.get(0).replace("/", "_"), module);
        	DashState gotoState = DashHelper.getState(trans.gotoExpr.gotoExpr.get(0).replace("/", "_"), module);
        	if (fromState == null || gotoState == null) {
        		continue;
        	}
        	DashConcState fromParent = getParentConcState(fromState);
        	DashConcState gotoParent = getParentConcState(gotoState);
        	if (fromParent == null || gotoParent == null) {
        		continue;
        	}
        	if (fromParent.getFullyQualName().equals(gotoParent.getFullyQualName())) {
        		continue;
        	}
        	Object immediateFromParent = getImmediateParent(fromState);
        	while (immediateFromParent != null) {
        		Object lookAhead = getImmediateParent(immediateFromParent);
        		if (lookAhead instanceof DashConcState) {
        			DashConcState concStateParent = (DashConcState) lookAhead;
        			if (concStateParent.getFullyQualName().equals(gotoParent.getFullyQualName())) {
        				trans.getOrigin().leavingMultipleStates = true;
        				break;
        			}
        		}
        		if (lookAhead instanceof DashState) {
        			DashState stateParent = (DashState) lookAhead;
        			if (stateParent.getFullyQualName().equals(gotoParent.getFullyQualName())) {
        				trans.getOrigin().leavingMultipleStates = true;
        				break;
        			}
        		}
        		immediateFromParent = getImmediateParent(immediateFromParent);
        	}
        	
        	if (trans.getOrigin().leavingMultipleStates) {
        		trans.getOrigin().fromExprs = immediateFromParent instanceof DashConcState ? new ArrayList<DashConcState>(getAllConcStates((DashConcState) immediateFromParent)) : new ArrayList<DashConcState>(getAllConcStates((DashState) immediateFromParent));
        		trans.getOrigin().stateBeingLeft = (immediateFromParent instanceof DashConcState) ? ((DashConcState) immediateFromParent).getFullyQualName() : ((DashState) immediateFromParent).getFullyQualName();
        		trans.getOrigin().concStateBeingExited = fromParent;
        	}
        }
    }
    
     List<DashConcState> getAllConcStates (DashState state) {
    	List<DashConcState> concStatesLeft = new ArrayList<DashConcState>();
    	for (DashState innerORState: state.getInnerORStates()) {
    		concStatesLeft.addAll(getAllConcStates(innerORState));
    	}
    	for (DashConcState innerANDState: state.getInnerConcStates()) {
    		concStatesLeft.addAll(getAllConcStates(innerANDState));
    	}
    	concStatesLeft.addAll(state.getInnerConcStates());
    	return concStatesLeft;
    }
    
     List<DashConcState> getAllConcStates (DashConcState concState) {
    	List<DashConcState> concStatesLeft = new ArrayList<DashConcState>();
    	
    	for (DashState innerORState: concState.getInnerORStates()) {
    		concStatesLeft.addAll(getAllConcStates(innerORState));
    	}
    	for (DashConcState innerANDState: concState.getInnerConcStates()) {
    		concStatesLeft.addAll(getAllConcStates(innerANDState));
    	}
    	concStatesLeft.addAll(concState.getInnerConcStates());
    	return concStatesLeft;
    }
    
     Object getImmediateParent(Object state) {
    	if (state instanceof DashConcState) {
    		return ((DashConcState) state).getParent();
    	}
    	if (state instanceof DashState) {
    		return ((DashState) state).getParent();
    	}
    	return null;
    }
     
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     String getDefaultState(DashState state) { 
    	for(DashState innerState: state.getInnerORStates()) {
    		if(innerState.isDefault())
    			return getDefaultState(innerState);
    	}

        return state.getFullyQualName();
    }
    
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     String getDefaultState(DashConcState state) { 
    	for(DashState innerState: state.getInnerORStates()) {
    		if(innerState.isDefault())
    			return getDefaultState(innerState);
    	}

        return state.getFullyQualName();
    }

    /* Check to see if a state that we are transitioning to has an inner default state,
    	if it does, then the transition will need to transition to that state instead
    */
     Map<String, DashConcState> getDefaultStates(DashConcState concState, DashModule module) {
    	Map<String, DashConcState> defaultStates = new LinkedHashMap<String, DashConcState>();
    	for (DashConcState innerConcState: concState.getInnerConcStates()) {
    		while (innerConcState.getInnerConcStates().size() > 0) {
    			innerConcState = innerConcState.getParentConcState();
    		}
    		DashState defaultState = DashHelper.getState(getDefaultState(innerConcState), module);
    		if ((defaultState != null) && (defaultState.getInnerConcStates().size() == 0)) {
    			defaultStates.put(defaultState.getFullyQualName(), innerConcState);
    		}
    	}
    	for(DashState innerState: concState.getInnerORStates()) {
    		if(innerState.isDefault() && innerState.getInnerConcStates().size() == 0) {
    			defaultStates.put(innerState.getFullyQualName(), concState);
    		}
    	}

        return defaultStates;
    }
    
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     Map<String, DashConcState> getDefaultStates(DashConcState concState, DashModule module, Map<String, DashConcState> defaultStates) {
    	for (DashConcState innerConcState: concState.getInnerConcStates()) {
    		getDefaultStates(innerConcState, module, defaultStates);
    	}
    	for (DashState state: concState.getInnerORStates()) {
    		if (state.isDefault()) {
    			if (state.getInnerConcStates().size() == 0) {
	    			defaultStates.put(state.getFullyQualName(), concState);
    			}
    			
    			for (DashConcState innerConcState: state.getInnerConcStates()) {
    				getDefaultStates(innerConcState, module, defaultStates);
    			}
    		}
    	}

        return defaultStates;
    }

    /* Fetch all the transitions in the model */
     private void getAllTransitions(DashModule module) {
        for (DashConcState concState : module.concStates.values()) {
            for (DashTrans transition : concState.getTransitions())
                addTrans(concState, transition, module);
            for (DashTemplateCall templateCall : concState.getTemplateCalls())
                addTemplateCall(concState, templateCall, module);
        }

        for (DashState state : module.states.values()) {
            for (DashTrans transition : state.getTransitions())
                addTrans(state, transition, module);
        }
    }

    /*
     * This is called by the getAllTransitions function once it finds a transition
     * inside an OR state
     */
     private void addTrans(DashState parent, DashTrans transition, DashModule module) {
        String modifiedTransName = parent.getFullyQualName() + '_' + transition.getRawName();
        transition.setFullyQualName(modifiedTransName);
        transition.setParent(parent);

        /*
         * If we have more than one from command (source), split up the transition such
         * that each transition represents one from command.
         */
        if (transition.getOrigin() != null && transition.getOrigin().fromExpr.size() > 0) {
            for (String fromExpr : transition.getOrigin().fromExpr) {
                if (transition.getRawName() == null)
                    modifiedTransName = parent.getFullyQualName() + "_t_" + (++transitionCount);
                generateTransition(transition, fromExpr, modifiedTransName, module);
            }
        } else {
            if (transition.getRawName() == null)
                modifiedTransName = parent.getFullyQualName() + "_t_" + (++transitionCount);
            transition.setFullyQualName(modifiedTransName);
            transition.setParentConcState(getParentConcState(parent));
            module.transitions.put(modifiedTransName, transition);
        }
    }
    
    /*
     * This is called by the getAllTransitions function once it finds a transition
     * inside an conc state
     */
     private void addTrans(DashConcState parent, DashTrans transition, DashModule module) {
    	String modifiedTransName = parent.getFullyQualName() + '_' + transition.getRawName();
        transition.setFullyQualName(modifiedTransName);
        transition.setParent(parent);

        /*
         * If we have more than one from command (source), split up the transition such
         * that each transition represents one from command.
         */
        if (transition.getOrigin() != null && transition.getOrigin().fromExpr.size() > 0) {
            for (String fromExpr : transition.getOrigin().fromExpr) {
                if (transition.getRawName() == null)
                    modifiedTransName = parent.getFullyQualName() + "_t_" + (++transitionCount);
                generateTransition(transition, fromExpr, modifiedTransName, module);
            }
        } else {
            if (transition.getRawName() == null)
                modifiedTransName = parent.getFullyQualName() + "_t_" + (++transitionCount);
            transition.setFullyQualName(modifiedTransName);
            transition.setParentConcState(parent);
            module.transitions.put(modifiedTransName, transition);
        }
    }

    /*
     * This is called by the addConcState function once it finds a transition
     * template call. It refers to the template being called and uses it to create
     * new transitions
     */
     private void addTemplateCall(DashConcState parent, DashTemplateCall templateCall, DashModule module) {
        DashTransTemplate transTemplate = module.transitionTemplates.get(templateCall.templateName);
        List<String> declNames = new ArrayList<String>();

        //Each decl is an argument for a template call
        for (Decl decl : transTemplate.decls) {
            declNames.add(decl.get().toString());
        }

        DashTrans trans = new DashTrans(null, templateCall.name, new ArrayList<Object>());
        trans.setParent(parent);

        //If we have an On command, check if it matches an argument. If it does, then set the on Command
        //to that of the argument
        if (transTemplate.onExpr != null) {
            if (declNames.indexOf(transTemplate.onExpr.getRawName()) != -1)
                trans.onExpr = new DashOn(null, templateCall.templateParam.get(declNames.indexOf(transTemplate.onExpr.getRawName())), checkInternalEvent(trans, module));
            else
                trans.onExpr = new DashOn(null, transTemplate.onExpr.getRawName(), checkInternalEvent(trans, module));
        }

        //If we have a From command, check if it matches an argument. If it does, then set the From Command
        //to that of the argument
        if (transTemplate.fromExpr != null && !transTemplate.fromExpr.fromAll) {
            List<String> fromExprList = new ArrayList<String>();

            for (String fromExpr : transTemplate.fromExpr.fromExpr) {
                if (declNames.indexOf(fromExpr) != -1)
                    fromExprList.add(templateCall.templateParam.get(declNames.indexOf(fromExpr)));
                else
                    fromExprList.add(fromExpr);
            }
            trans.setOrigin(new DashFrom(fromExprList, false));
        }

        //If we have a Goto command, check if it matches an argument. If it does, then set the Goto Command
        //to that of the argument
        if (transTemplate.gotoExpr != null) {
            if (declNames.indexOf(transTemplate.gotoExpr.gotoExpr.get(0)) != -1)
                trans.gotoExpr = new DashGoto(templateCall.templateParam.get(declNames.indexOf(transTemplate.gotoExpr.gotoExpr.get(0))));
            else
                trans.gotoExpr = new DashGoto(transTemplate.gotoExpr.gotoExpr);
        }

        //If we have a Send command, check if it matches an argument. If it does, then set the Send Command
        //to that of the argument
        if (transTemplate.sendExpr != null) {
            if (declNames.indexOf(transTemplate.sendExpr.getRawName()) != -1)
                trans.sendExpr = new DashSend(null, templateCall.templateParam.get(declNames.indexOf(transTemplate.sendExpr.getRawName())));
            else
                trans.sendExpr = new DashSend(null, transTemplate.sendExpr.getRawName());
        }

        //If we have a do command, add it to our transition
        if (transTemplate.doExpr != null) {
            trans.doExpr = new DashDoExpr(null, transTemplate.doExpr.expr);
        }

        //If we have a when command, add it to our transition
        if (transTemplate.whenExpr != null) {
            trans.whenExpr = new DashWhenExpr(null, transTemplate.whenExpr.expr);
        }

        //If the from command is: from *, then we need to fetch all the Or states in the conc state,
        //and create new transitions each with a different or state as the source
        if (transTemplate.fromExpr != null && transTemplate.fromExpr.fromAll) {
            for (DashState state : parent.getInnerORStates()) {
                trans.setOrigin(new DashFrom(state.getRawName(), false));
                trans.setFullyQualName(parent.getFullyQualName() + "_" + templateCall.name + "__" + (++transitionCount));
                trans.setParentConcState(parent);
                module.transitions.put(trans.getFullyQualName(), new DashTrans(trans));
            }
        } //If we have more than one From command, create a new transition for each for command
        else if (transTemplate.fromExpr != null && trans.getOrigin().fromExpr.size() > 0) {
            for (String fromExpr : trans.getOrigin().fromExpr)
                generateTransition(trans, fromExpr, parent.getFullyQualName() + "_" + templateCall.name + "__" + (++transitionCount), module);
        } else {
        	trans.setFullyQualName(parent.getFullyQualName() + "_" + templateCall.name + "__" + (++transitionCount));
            trans.setParentConcState(parent);
            module.transitions.put(trans.getFullyQualName(), trans);
        }
    }

     private void generateTransition(DashTrans transition, String fromExpr, String modifiedName, DashModule module) {
        DashTrans trans = new DashTrans(transition); // New transition representing one of the From commands
        trans.setOrigin(new DashFrom(fromExpr, false)); // Add the from command to the new transition
        trans.setFullyQualName(modifiedName);
        trans.setParentConcState(getParentConcState(transition.getParent()));
        module.transitions.put(modifiedName, trans);
    }

     DashDoExpr addAction(DashDoExpr doExpr, DashModule module) {
        if (doExpr != null) {
            if (doExpr.expr instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) doExpr.expr;
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar)
                            doExpr.exprList.add(getActionExpr(expression, module));
                        else
                            doExpr.exprList.add(expression);

                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    doExpr.exprList.add(getActionExpr(parentExprUnary.sub, module));
                else
                    doExpr.exprList.add(parentExprUnary.sub);
            } else {
                doExpr.exprList.add(doExpr.expr);
            }
        }
        return doExpr;
    }

     DashWhenExpr addCondition(DashWhenExpr whenExpr, DashModule module) {
        if (whenExpr != null) {
            if (whenExpr.expr instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) whenExpr.expr;
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar) {
                            whenExpr.exprList.add(getActionExpr(expression, module));
                        } else {
                            whenExpr.exprList.add(expression);
                        }
                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    whenExpr.exprList.add(getConditionExpr(parentExprUnary.sub, module));
                else
                    whenExpr.exprList.add(parentExprUnary.sub);
            } else {
                whenExpr.exprList.add(whenExpr.expr);
            }
        }
        return whenExpr;
    }

     Expr getActionExpr(Expr expr, DashModule module) {
        for (DashAction value : module.actions.values()) {
            if (expr.toString().equals(value.name))
                return value.expr;
        }
        return expr;
    }

     Expr getConditionExpr(Expr expr, DashModule module) {
        for (DashCondition value : module.conditions.values()) {
            if (expr.toString().equals(value.getRawName()))
                return value.getExpr();
        }
        return expr;
    }

     DashOn completeOnCommand(DashTrans trans, DashModule module) {
        if (trans.onExpr == null)
            return null;

        DashOn on = new DashOn(trans.onExpr);
        String onCommand = trans.onExpr.getRawName();

        if (onCommand.contains("/")) {
            onCommand = onCommand.substring(onCommand.indexOf('/') + 1);
        }

        for(DashConcState concState: module.concStates.values()) {
        	for(DashEvent event: concState.getEvents()) {
        		if(event.getRawName().equals(onCommand)) {
        			on.setParentConcState(concState);
        			onCommand = (concState.getFullyQualName() + "_" + onCommand);
        		}
        	}
        }

        DashConcState onParent = on.getParentConcState() == null? trans.getParentConcState() : on.getParentConcState();
        on.setRawName(onCommand);
        on.isInternal = checkInternalEvent(trans, module);
        return on;
    }

     DashSend completeSendCommand(DashTrans trans, DashModule module) {
        if (trans.sendExpr == null)
            return null;

        DashSend send = new DashSend(trans.sendExpr);
        String sendCommand = trans.sendExpr.getRawName();
        Object eventParentObj = trans.getParent();

        if (sendCommand != null && sendCommand.contains("/")) {
            sendCommand = sendCommand.substring(sendCommand.indexOf('/') + 1);
        }

        while (eventParentObj != null) {
            if (eventParentObj instanceof DashConcState) {
            	if (checkForEvent((DashConcState) eventParentObj, sendCommand)) {
            		send.setParentConcState((DashConcState) eventParentObj);
            		sendCommand = ((DashConcState) eventParentObj).getFullyQualName() + "_" + sendCommand;
            	}
            }

            eventParentObj = getParent(eventParentObj);
        }
        
        send.setRawName(sendCommand);
        DashConcState sendParent = send.getParentConcState() == null ? trans.getParentConcState() : send.getParentConcState();
        send.setParentConcState(sendParent);
        return send;
    }   
    
     Boolean checkInternalEvent(DashTrans trans, DashModule module)
    {
        if (trans.onExpr == null)
            return false;
    	
        String onCommand = trans.onExpr.getRawName();

        if (onCommand.contains("/")) 
            onCommand = onCommand.substring(onCommand.lastIndexOf('/') + 1);

        for(DashConcState concState: module.concStates.values()) {
        	for(DashEvent event: concState.getEvents()) {
        		if(event.type.equals("event") && event.getRawName().equals(onCommand)) {
        			return true;
        		}
        	}
        }  
        return false;
    }
    
     Boolean checkForEvent(DashConcState concState, String eventName) {
    	for (DashEvent event: concState.getEvents()) {
    		if (event.getRawName().equals(eventName)) 
    			return true;
    		
    	}
    	return false;
    }

     List<String> completeFromCommand(DashTrans trans, DashModule module) {
        List<String> completedFromCommands = new ArrayList<String>();

        if (trans.getOrigin() != null) {
            for (String fromCommand : trans.getOrigin().fromExpr) {
            	if(fromCommand.contains("/"))
            		fromCommand = fromCommand.substring(fromCommand.lastIndexOf("/") + 1);
            	
            	DashState fromState = locateState(trans, fromCommand, module);
            	
            	if(fromState != null)
            		completedFromCommands.add(fromState.getFullyQualName());
            	else /* Transitioning to a conc state that does not have an OR state */
            		completedFromCommands.add(generateCompleteCommand(trans, fromCommand));
            }
        } else {
            completedFromCommands.add(generateCompleteCommand(trans, ""));
        }
        
        return completedFromCommands;
    }

     DashGoto completeGoToCommand(DashTrans trans, DashModule module) {
        List<String> completedGoToCommands = new ArrayList<String>();

        if (trans.gotoExpr != null && trans.gotoExpr.gotoExpr != null) {
            for (String gotoCommand : trans.gotoExpr.gotoExpr) {
            	if(gotoCommand.contains("/")) {
            		completedGoToCommands.add(gotoCommand);
            		return new DashGoto(trans.gotoExpr.pos, completedGoToCommands, trans.gotoExpr.param);
            	}
            	
            	DashState gotoState = locateState(trans, gotoCommand, module);
            	
            	if(gotoState != null) {
            		completedGoToCommands.add(gotoState.getFullyQualName());
            	}
            	else /* Transitioning to a conc state that does not have an OR state */
            		completedGoToCommands.add(generateCompleteCommand(trans, gotoCommand));
            }
        }
        else {
            //If we do not have a goto command, it should be equal to the origin of the transition
            completedGoToCommands.add(trans.getOrigin().fromExpr.get(0));
        }
 
        return trans.gotoExpr == null ? new DashGoto(null, completedGoToCommands, null) : new DashGoto(trans.gotoExpr.pos, completedGoToCommands, trans.gotoExpr.param);
    }
    
    /* Locate an or state to transition to  */
     DashState locateState(DashTrans trans, String command, DashModule module) {
    	DashConcState parent = getParentConcState(trans.getParent());
    	List<DashState> states = new ArrayList<DashState>();
    	while(parent != null) {
    		for(DashState state: parent.getInnerORStates()) {
    			states.add(state);   			
    			if(state.getInnerORStates().size() > 0)
    				getInnerStates(state, states);
    		}		
    		for(DashState state: states) {
    			if(state.getRawName().equals(command))
    				return state;
    		}
    		
    		parent = getParentConcState(parent);
    	}
    	
    	return null;
    }
    
     private void getInnerStates(DashState state, List<DashState> states) {
		for(DashState innerState: state.getInnerORStates()) {	
			states.add(innerState);
			
			if(innerState.getInnerORStates().size() > 0)
				getInnerStates(innerState, states);
		}
    }
    
     private String generateCompleteCommand(Object transItem, String expr) {
        String completeCommand = "";
        Object parentObject = null;

        if (transItem instanceof DashTrans)
            parentObject = ((DashTrans) transItem).getParent();
        if (transItem instanceof DashState)
            parentObject = ((DashState) transItem).getParent();
        if (transItem instanceof DashConcState)
            parentObject = ((DashConcState) transItem).getParentORState();

        while (parentObject != null) {
            if (parentObject instanceof DashConcState) {
                completeCommand = ((DashConcState) parentObject).getRawName() + "/" + completeCommand;
                parentObject = getParent(parentObject);
            } else if (parentObject instanceof DashState) {
                completeCommand = ((DashState) parentObject).getRawName() + "/" + completeCommand;
                parentObject = getParent(parentObject);
            }
        }       

        completeCommand = completeCommand + expr;

        if (completeCommand.substring(completeCommand.length() - 1).equals("/")) // If the last character is a /, then remove it
            completeCommand = completeCommand.substring(0, completeCommand.length() - 1);
        
        return completeCommand;
    }
    
    private  DashConcState getParentConcState(Object item) { 	
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

     Object getParent(Object parent) {
        if (parent instanceof DashState)
            return ((DashState) parent).getParent();
        if (parent instanceof DashConcState)
            return ((DashConcState) parent).getParent();
        return null;
    }
}