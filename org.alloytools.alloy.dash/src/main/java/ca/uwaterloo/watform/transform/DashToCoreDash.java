package ca.uwaterloo.watform.transform;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

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
import ca.uwaterloo.watform.ast.DashSuperState;
import ca.uwaterloo.watform.ast.DashTemplateCall;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.ast.DashTransTemplate;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashHelper.ItemType;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.ast.Decl;


import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashToCoreDash {   
    public DashToCoreDash() {}
    
    public DashModule transformToCoreDash(final DashModule module, final String fileName, final String path) throws IOException {
    	DashModule coreDashModule = new DashModule(module, fileName, path, true);
        modifyTransitions(coreDashModule);
        modifyGoToCommands(coreDashModule); 
        modifyFromCommands(coreDashModule);
        modifyTransitionParent(coreDashModule);
        return coreDashModule;
    }

     private void modifyTransitions(final DashModule module) {
        for (DashTrans trans : module.getTransitions().values()) {
            trans.setOrigin(new DashFrom(completeFromCommand(trans, module), false));
            trans.setDestination(completeGoToCommand(trans, module));
            trans.setTriggerEvent(completeOnCommand(trans, module));
            trans.setEventsTriggered(completeSendCommand(trans, module));
            trans.setAction(addAction(trans.getAction(), module));
            trans.setCondition(addCondition(trans.getCondition(), module));
        }
    }
      
    /* Check the source state of a transition, and set that source state as its parent. Simplifies the 
     * CoreDash to Alloy AST conversion. Then add this transition to the list of transitions for that state */
     private void modifyTransitionParent(final DashModule module) {
        for (DashTrans trans : module.getTransitions().values()) {
        	DashState sourceState = DashHelper.getState(trans.getOrigin().getAllOrigins().get(0).replace("/", "_"), module); 	
        	if (sourceState != null) {
        		trans.setParent(sourceState);
        		
        		for(DashState state: module.getORStates().values()) {
        			if(state.getFullyQualName().equals(sourceState.getFullyQualName())) {
        				state.addModifiedTransition(trans);
        			}
        		}
        	}     	
        } 
    } 
    
    /* Check if a GoTo command transitions to a state that has inner OR states. If so,
     * then that transition will need to transition to the default inner OR state */
     private void modifyGoToCommands(final DashModule module) { 
        for (DashTrans trans : module.getTransitions().values()) {
        	String destination = trans.getDestination().getAllDestinations().get(0);
        	DashState destinationState = DashHelper.getState(destination, module);
        
        	if (destinationState == null) {
        		List<DashSuperState> match = new ArrayList<>();
        		// Get the parent AND state of the OR state we want to visit
        		DashHelper.findItemParentLocally(trans.getParentConcState(), destination, match);
        		Optional<DashSuperState> destinationOR = Optional.empty();
        		if (match.size() > 0) {
        			String ref = destination.substring(destination.indexOf('/') + 1);
        			// Locate the OR state being referenced
        			destinationOR = DashHelper.locateItem(module, ref, match.get(0), DashHelper.ItemType.ORSTATE);
        		}
        			
        		destinationState = (destinationOR.isPresent() && destinationOR.get() instanceof DashState) ? (DashState) destinationOR.get() : destinationState;
        	}

        	String defaultInnerState;
        	/* destState is null if the destination state is a concurrent state (it has no OR states) */
        	if(destinationState != null && destinationState.getInnerConcStates().size() == 0) {
        		defaultInnerState = getDefaultState(destinationState, trans.getDestination().getAllStatesEntered());
        		trans.getDestination().setParentConcState(DashHelper.getParentConcState(destinationState));
        		trans.setDestination(trans.getDestination().getDestination() == null ? new DashGoto(new ArrayList<String>(Arrays.asList(defaultInnerState)), trans.getDestination().getAllStatesEntered()) 
        				: new DashGoto(null, new ArrayList<String>(Arrays.asList(defaultInnerState)), trans.getDestination().getDestination(), trans.getDestination().getAllStatesEntered()));
        	} 
        	else if (destinationState != null && destinationState.getInnerConcStates().size() > 0) {
        		Map<String, DashConcState> defaultStates = new LinkedHashMap<String, DashConcState>();
        		for (DashConcState innerConcState: destinationState.getInnerConcStates()) {
        			Map<String, DashConcState> defaultState = new LinkedHashMap<String, DashConcState>(getDefaultStates(innerConcState, module, new LinkedHashMap<String, DashConcState>(), trans.getDestination().getAllStatesEntered()));
        			for (String key: defaultState.keySet()) {
        				defaultStates.put(key, defaultState.get(key));
        			}
        		}
    			trans.getDestination().setDefaultStatesEntered(new LinkedHashMap<String, DashConcState>(defaultStates));
    			trans.getDestination().setEnteringDefaultStates(true);
        	}
        }
    } 
    
    /* Check if leave a state will result in other concurrent states leaving their current state */
     private void modifyFromCommands(final DashModule module) {
        for (DashTrans trans : module.getTransitions().values()) {
        	DashState fromState = DashHelper.getState(trans.getOrigin().getAllOrigins().get(0).replace("/", "_"), module);
        	DashState gotoState = DashHelper.getState(trans.getDestination().getAllDestinations().get(0).replace("/", "_"), module);
        	if (fromState == null || gotoState == null) {
        		continue;
        	}
        	DashConcState fromParent = DashHelper.getParentConcState(fromState);
        	DashConcState gotoParent = DashHelper.getParentConcState(gotoState);
        	if (fromParent == null || gotoParent == null) {
        		continue;
        	}
        	if (fromParent.getFullyQualName().equals(gotoParent.getFullyQualName())) {
        		continue; 
        	}
        	DashSuperState immediateFromParent = fromState.getParent();
        	while (immediateFromParent != null) {
        		DashSuperState lookAhead = immediateFromParent.getParent();
    			DashSuperState stateParent = lookAhead;
    			if (stateParent.getFullyQualName().equals(gotoParent.getFullyQualName())) {
    				trans.getOrigin().setLeavingMultipleStates(true);
    				break;
    			}
        		immediateFromParent = immediateFromParent.getParent();
        	}
        	
        	if (trans.getOrigin().isTransitionToParentState()) {
        		trans.getOrigin().setConcStatesExited(immediateFromParent instanceof DashConcState ? new ArrayList<DashConcState>(getAllConcStates((DashConcState) immediateFromParent)) 
        				: new ArrayList<DashConcState>(getAllConcStates((DashState) immediateFromParent)));
        		trans.getOrigin().setStateBeingLeft((immediateFromParent instanceof DashConcState) ? ((DashConcState) immediateFromParent).getFullyQualName() 
        				: ((DashState) immediateFromParent).getFullyQualName());
        		trans.getOrigin().setConcStateExited(fromParent);
        	}
        }
    }
    
     List<DashConcState> getAllConcStates (final DashSuperState state) {
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
    
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     String getDefaultState(final DashState state, List<DashState> statesEntered) { 
    	for(DashState innerState: state.getInnerORStates()) {
    		if(innerState.isDefault()) {
    			statesEntered.add(state);
    			return getDefaultState(innerState, statesEntered);
    		}
    	}

        return state.getFullyQualName();
    } 
    
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     String getDefaultState(final DashConcState state, List<DashState> statesEntered) { 
    	for(DashState innerState: state.getInnerORStates()) {
    		if(innerState.isDefault())
    			return getDefaultState(innerState, statesEntered);
    	}

        return state.getFullyQualName();
    }

    /* Check to see if a state that we are transitioning to has an inner default state,
    	if it does, then the transition will need to transition to that state instead
    */
     Map<String, DashConcState> getDefaultStates(final DashConcState concState, final DashModule module, List<DashState> statesEntered) {
    	Map<String, DashConcState> defaultStates = new LinkedHashMap<String, DashConcState>();
    	for (DashConcState innerConcState: concState.getInnerConcStates()) {
    		while (innerConcState.getInnerConcStates().size() > 0) {
    			innerConcState = innerConcState.getParentConcState();
    		}
    		DashState defaultState = DashHelper.getState(getDefaultState(innerConcState, statesEntered), module);
    		if ((defaultState != null) && (defaultState.getInnerConcStates().size() == 0)) {
    			defaultStates.put(defaultState.getFullyQualName(), innerConcState);
    		}
    	}
    	for(DashState innerState: concState.getInnerORStates()) {
    		if(innerState.isDefault() && innerState.getInnerConcStates().size() == 0 && innerState.getInnerORStates().size() == 0) {
    			defaultStates.put(innerState.getFullyQualName(), concState);
    		}
    		else if (innerState.isDefault() && innerState.getInnerORStates().size() > 0) {
    			defaultStates.put(getDefaultState(innerState, statesEntered), concState);
    		}
    	}

        return defaultStates;
    }
    
    //Check to see if a state that we are transitioning to has an inner default state,
    //if it does, then the transition will need to transition to that state instead
     Map<String, DashConcState> getDefaultStates(final DashConcState concState, final DashModule module, final Map<String, DashConcState> defaultStates, List<DashState> statesEntered) {
    	for (DashConcState innerConcState: concState.getInnerConcStates()) {
    		getDefaultStates(innerConcState, module, defaultStates, statesEntered);
    	}
    	for (DashState state: concState.getInnerORStates()) {
    		if (state.isDefault()) {
    			if (state.getInnerConcStates().size() == 0 && state.getInnerORStates().size() == 0) {
	    			defaultStates.put(state.getFullyQualName(), concState);
    			}
    			else if (state.getInnerConcStates().size() == 0 && state.getInnerORStates().size() > 0) {
    				defaultStates.put(getDefaultState(state, statesEntered), concState);
    			}
    			
    			for (DashConcState innerConcState: state.getInnerConcStates()) {
    				getDefaultStates(innerConcState, module, defaultStates, statesEntered);
    			}
    		}
    	}

        return defaultStates;
    }

     DashDoExpr addAction(final DashDoExpr doExpr, final DashModule module) {
        if (doExpr != null) {
            if (doExpr.getExpr() instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) doExpr.getExpr();
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar)
                            doExpr.getAllExpression().add(getActionExpr(expression, module));
                        else
                            doExpr.getAllExpression().add(expression);

                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    doExpr.getAllExpression().add(getActionExpr(parentExprUnary.sub, module));
                else
                    doExpr.getAllExpression().add(parentExprUnary.sub);
            } else {
                doExpr.getAllExpression().add(doExpr.getExpr());
            }
        }
        return doExpr;
    }

     DashWhenExpr addCondition(final DashWhenExpr whenExpr, final DashModule module) {
        if (whenExpr != null) {
            if (whenExpr.getExpr() instanceof ExprUnary) {
                ExprUnary parentExprUnary = (ExprUnary) whenExpr.getExpr();
                if (parentExprUnary.sub instanceof ExprList) {
                    ExprList exprList = (ExprList) parentExprUnary.sub;
                    for (Expr expression : exprList.args) {
                        if (expression instanceof ExprVar) {
                            whenExpr.getAllExpressions().add(getActionExpr(expression, module));
                        } else {
                            whenExpr.getAllExpressions().add(expression);
                        }
                    }
                } else if (parentExprUnary.sub instanceof ExprVar)
                    whenExpr.getAllExpressions().add(getConditionExpr(parentExprUnary.sub, module));
                else
                    whenExpr.getAllExpressions().add(parentExprUnary.sub);
            } else {
                whenExpr.getAllExpressions().add(whenExpr.getExpr());
            }
        }
        return whenExpr;
    } 

     Expr getActionExpr(final Expr expr, final DashModule module) {
        for (DashAction value : module.getActions().values()) {
            if (expr.toString().equals(value.getRawName()))
                return value.getAction();
        }
        return expr;
    }

     Expr getConditionExpr(final Expr expr, final DashModule module) {
        for (DashCondition value : module.getConditions().values()) {
            if (expr.toString().equals(value.getRawName()))
                return value.getExpr();
        }
        return expr;
    }
 
     DashOn completeOnCommand(final DashTrans trans, final DashModule module) {
        if (trans.getTriggerEvent() == null)
            return null;

        DashOn on = new DashOn(trans.getTriggerEvent());
        String onCommand = trans.getTriggerEvent().getRawName();
        
    	List<DashSuperState> match = new ArrayList<>();
    	Optional<DashSuperState> actualParent = Optional.empty();
        if (onCommand != null && onCommand.contains("/")) {
        	DashHelper.findItemParentLocally(trans.getParentConcState(), onCommand, match);
        	if (match.size() > 0) {
        		on.setParent(match.get(0));
        		on.setParentConcState(match.get(0).getANDState());
        		on.setRawName(match.get(0).getFullyQualName() + '_' + onCommand.substring(onCommand.lastIndexOf('/') + 1)); 	
        	} else {
        		throw new ErrorSyntax("Could not resolve reference to: " + onCommand);
        	}
        } else {
        	actualParent = DashHelper.findEventParent(trans.getParentConcState(), onCommand);
        	if (!actualParent.isPresent()) {
        		actualParent = DashHelper.findEventParent(DashHelper.getTopLevelConcStates(trans.getParentConcState()), onCommand);
        	}
        	if (!actualParent.isPresent()) {
        		throw new ErrorSyntax("Could not resolve reference to: " + onCommand);
        	}
        	
        	on.setRawName(actualParent.get().getFullyQualName() + '_' + onCommand);
        	on.setParentConcState(actualParent.get().getANDState());
        }
        on.setIsInternal(DashHelper.checkInternalEvent(trans, module));      
        return on;
    }

     DashSend completeSendCommand(final DashTrans trans, final DashModule module) {
        if (trans.getEventsTriggered() == null) {
            return null;
        }

        DashSend send = new DashSend(trans.getEventsTriggered());
        String sendCommand = trans.getEventsTriggered().getRawName();

    	List<DashSuperState> match = new ArrayList<>();
    	Optional<DashSuperState> actualParent = Optional.empty();
        if (sendCommand != null && sendCommand.contains("/")) {
        	DashHelper.findItemParentLocally(trans.getParentConcState(), sendCommand, match);
        	if (match.size() > 0) {
        		send.setParent(match.get(0));
        		send.setParentConcState(match.get(0).getANDState());
        		send.setRawName(match.get(0).getFullyQualName() + '_' + sendCommand.substring(sendCommand.lastIndexOf('/') + 1)); 	
        	} else {
        		throw new ErrorSyntax("Could not resolve reference to: " + sendCommand);
        	}
        } else {
        	actualParent = DashHelper.findEventParent(trans.getParentConcState(), sendCommand);
        	if (!actualParent.isPresent()) {
        		actualParent = DashHelper.findEventParent(DashHelper.getTopLevelConcStates(trans.getParentConcState()), sendCommand);
        	}
        	if (!actualParent.isPresent()) {
        		throw new ErrorSyntax("Could not resolve reference to: " + sendCommand);
        	}
        	
        	send.setRawName(actualParent.get().getFullyQualName() + '_' + sendCommand);
            send.setParentConcState(actualParent.get().getANDState());
        }
        
        return send;
    }
    
     Boolean checkForEvent(final DashConcState concState, final String eventName) {
    	for (DashEvent event: concState.getEvents()) {
    		if (event.getRawName().equals(eventName)) 
    			return true;
    		
    	}
    	return false;
    }

     List<String> completeFromCommand(final DashTrans trans, final DashModule module) {
        List<String> completedFromCommands = new ArrayList<String>();

        if (trans.getOrigin() != null) {
            for (String fromCommand : trans.getOrigin().getAllOrigins()) {
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

     DashGoto completeGoToCommand(final DashTrans trans, final DashModule module) {
        List<String> completedGoToCommands = new ArrayList<String>();

        if (trans.getDestination() != null && trans.getDestination().getAllDestinations() != null) {
            for (String gotoCommand : trans.getDestination().getAllDestinations()) {
            	if(gotoCommand.contains("/")) {
            		completedGoToCommands.add(gotoCommand);
            		return new DashGoto(trans.getDestination().getPos(), completedGoToCommands, trans.getDestination().getDestination());
            	}
            	
            	DashState gotoState = locateState(trans, gotoCommand, module);
            	
            	if(gotoState != null) {
            		completedGoToCommands.add(gotoState.getFullyQualName());
            	}
            	else {/* Transitioning to a conc state that does not have an OR state */
            		completedGoToCommands.add(generateCompleteCommand(trans, gotoCommand));
            	}
            }
        }
        else {
            //If we do not have a goto command, it should be equal to the origin of the transition
            completedGoToCommands.add(trans.getOrigin().getAllOrigins().get(0));
        }
 
        return trans.getDestination() == null ? new DashGoto(null, completedGoToCommands, null) : new DashGoto(trans.getDestination().getPos(), completedGoToCommands, trans.getDestination().getDestination());
    }
    
    /* Locate an or state to transition to  */
     DashState locateState(final DashTrans trans, final String command, final DashModule module) {
    	DashConcState parent = DashHelper.getParentConcState(trans.getParent());
    	List<DashState> states = new ArrayList<DashState>();
    	while(parent != null) {
    		for(DashState state: parent.getInnerORStates()) {
    			states.add(state);   			
    			if(state.getInnerORStates().size() > 0)
    				DashHelper.getInnerStates(state, states);
    		}		
    		for(DashState state: states) {
    			if(state.getRawName().equals(command))
    				return state;
    		}
    		
    		parent = DashHelper.getParentConcState(parent);
    	}
    	
    	return null;
    }
    
     private String generateCompleteCommand(final Object transItem, final String expr) {
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
                parentObject = DashHelper.getParent(parentObject);
            } else if (parentObject instanceof DashState) {
                completeCommand = ((DashState) parentObject).getRawName() + "/" + completeCommand;
                parentObject = DashHelper.getParent(parentObject);
            }
        }       

        completeCommand = completeCommand + expr;

        if (completeCommand.substring(completeCommand.length() - 1).equals("/")) // If the last character is a /, then remove it
            completeCommand = completeCommand.substring(0, completeCommand.length() - 1);
        
        return completeCommand;
    }
}