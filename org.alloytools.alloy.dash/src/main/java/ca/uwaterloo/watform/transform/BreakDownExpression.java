package ca.uwaterloo.watform.transform;

import java.io.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import ca.uwaterloo.watform.ast.DashAction;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashCondition;
import ca.uwaterloo.watform.ast.DashSuperState;
import ca.uwaterloo.watform.ast.DashTrans;
import ca.uwaterloo.watform.parser.DashHelper;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class BreakDownExpression {
	CoreDashToAlloy current;
	
	public BreakDownExpression(CoreDashToAlloy current) {
		this.current = current;
	}
	
   /****************************** Retrieving Variables in Expressions *****************************/
    
    Expr getVarFromParentExpr(Expr parentExpr, DashConcState parent, DashModule module) {

        Expr ret = null;
        if (parentExpr instanceof ExprBinary) {
            ExprBinary exprBinary = (ExprBinary) parentExpr;
            ret = getVarFromBinary(exprBinary, parent, module);
        }
        if (parentExpr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) parentExpr;
            ret = getVarFromUnary(unary, parent, module, false);
        }
        if (parentExpr instanceof ExprBadJoin) {
        	ret =  getVarFromBadJoin((ExprBadJoin) parentExpr, parent, module);
        }
        if (parentExpr instanceof ExprQt) {
            ret = getVarFromExprQt((ExprQt) parentExpr, parent, module, new ArrayList<Decl>(), false);
        }
        if (parentExpr instanceof ExprVar) {
        	ret = modifyExprWithVar((ExprVar) parentExpr, parent, module, false);
        }
        if (parentExpr instanceof ExprList) {
        	ret = getVarFromExprList((ExprList) parentExpr, parent, module, false);
        }
        if (parentExpr instanceof ExprConstant) {
        	ret = (Expr) parentExpr;
        }
        // defensive programming
        if (ret == null) {
            throw new NullPointerException("BreakDownExpression.getVarFromParentExpr");
        } else {
            return ret;
        }

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

        Expr ret = DashHelper.createBinaryExpr(left, binary.op, right);
        // defensive programming
        if (ret == null) {
            throw new NullPointerException("DashHelper.getVarFromBinary left="+left+" op="+binary.op+"right="+right);
        } else {
            return ret;
        }

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
        
        ExprITE ret = (ExprITE) ExprITE.make(null, cond, left, right);
        // defensive programming
        if (ret == null) {
            throw new NullPointerException("BreakDownExpression.getVarFromITE left="+left+" cond="+cond+"right="+right);
        } else {
            return ret;
        }
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

        ExprUnary ret =  DashHelper.createUnaryExpr(unary.op, sub);
        // defensive programming
        if (ret == null) {
            throw new NullPointerException("DashHelper.getVarFromUnary unary="+unary);
        } else {
            return ret;
        }
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
        
        if (current.refParamChanged) {
        	current.refParamChanged = false;
        }

        if (current.paramBuffer.size() > 0) {
        	right = ExprBadJoin.make(null, null, left, right); //(pid.s.bufferName).add
        	Expr bufferName = DashHelper.createExprVar(current.paramBuffer.keySet().stream().findFirst().get());
        	Expr sNextJoinBuffer = DashOptions.isElectrum ? DashHelper.sVarPrimed(bufferName) : DashHelper.sNextVar(bufferName); //s_next.bufferName
        	left = ExprBadJoin.make(null, null, current.paramBuffer.get(current.paramBuffer.keySet().stream().findFirst().get()), sNextJoinBuffer); //(pid.s_next.bufferName)
        	current.paramBuffer.clear();
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
    	current.isCreatingExprQt = true;
	
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

        current.isCreatingExprQt = false;
        
        return DashHelper.createExprQt(exprQt.op, decls, subExpr);
    }
    
    
    /*************************************** MODIFY EXPRESSIONS WITH VARS ***************************************/

    //Take an expression in a do statement and modify any variables present. Eg: active_players should become
    //s.Game_active_players (Given that active_players is declared under the Game AND-state)
    private Expr modifyExprWithVar(Expr expr, DashConcState parent, DashModule module, Boolean isRef) {
    	DashConcState parentConcState = parent;
        Expr expression = expr; 
        
        /* If the var refers to a parameterizerd concurrent process, return 'p' as this refers to the current process */
        if(expression.toString().equals("this")) {
        	return current.isCreatingInit && parent.isParameterized() ? ExprVar.make(null, "p" + module.getIdentifierElements().indexOf(parent.getReplicatedIdentifier())) : 
        		ExprVar.make(null, "p0");
        }
        
        //If we make a reference to a conc state outside of the current conc state, find it and 
        //modify the value of the expression accordingly
    	if(expr.toString().contains("/")) {
    		String expressionStr = expr.toString();
    		Optional<DashSuperState> variableParent = DashHelper.findVariableParentByReference(module, parent, expressionStr);
    		if (variableParent.isPresent()) {
    			// Get the AND state in which the variable is located (if it is located in an OR state, then we 
    			// get the parent AND state of the OR state
    			DashSuperState immediateParent = variableParent.get();
    			// Get the name of the variable (ANDState/ORState/var) -> var
    			String variable = expressionStr.substring(expressionStr.lastIndexOf('/') + 1);
    			Expr exprVar = DashHelper.createExprVar(variable);
    			// Get all the variables
    	        expression = modifyVar(module, expression, immediateParent, exprVar, false, true);
    			return expression; 
    		}
    	} 
    	
    	// Check whether the expression variable is a variable declared in an AND-or OR-state
    	Optional<DashSuperState> variableParent = DashHelper.findVariableParent(module, parentConcState, expression.toString());
    	if (variableParent.isPresent()) {
    		expression = modifyVar(module, expression, variableParent.get(), expression, false, false);
    	} 

        //for (DashSuperState state: DashHelper.getNestedStates(DashHelper.getTopLevelConcStates(parentConcState))) {
        //	expression = modifyVar(module, expression, state.getANDState(), state, expr, DashHelper.getVariables(module, state), false, isRef);
        //}
    	/*
        // Look for the variable in nested AND-states
        for (DashConcState innerConcState: DashHelper.getNestedConcStates(parentConcState)) {
        	expression = modifyVar(module, expression, innerConcState, expr, false, isRef);
        }

        // Look for the variable in parent AND-states
        DashConcState outerConcState = DashHelper.getTopLevelConcState(parentConcState);
        while (outerConcState != null) {
        	expression = modifyVar(module, expression, outerConcState, expr, DashHelper.getVariables(module, outerConcState), false, isRef);
            outerConcState = outerConcState.getParentConcState();
        }
        */

        expression = replaceWithActionExpr(expression, parentConcState, module);
        expression = replaceWithConditionExpr(expression, parentConcState, module);
        
        return expression;
    }
        
    private Expr modifyVar(DashModule module, Expr expression, DashSuperState parent, Expr expr, boolean isEnvVar, boolean isRef) {
    	// Check if the var expression is a variable that has been declared in an AND- or OR-state
        for (String var : parent.getVariableNames()) {
        	var = var.replace('/', '_');
        	expr = DashHelper.createExprVar(expr.toString().replace('/', '_'));
        	String qualifiedVarName = parent.getFullyQualName() + '_' + var;
            if (expr.toString().equals(var + "'")) {
            	current.changedVars.put(qualifiedVarName, parent);
            	if (!isRef) {
            		current.changedLocalVars.put(qualifiedVarName, parent);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);
            		Expr sNextVar = DashHelper.createBinaryExpr(DashHelper.sNext(), ExprBinary.Op.JOIN, variable);
            		sNextVar = DashHelper.addParametersJoin(sNextVar, parent.getANDState().getIdentifiers().size());
            		return sNextVar;
            	}
            	else {
            		current.changedRefVars.add(qualifiedVarName);
            		Expr variable = DashHelper.createExprVar(qualifiedVarName);         	
            		Expr sNextVar = DashOptions.isElectrum ? DashHelper.sVarPrimed(variable) : DashHelper.createBinaryExpr(DashHelper.sNext(), ExprBinary.Op.JOIN, variable);
            		sNextVar = parent.getANDState().getIdentifiers() != null ? DashHelper.addParametersJoin(sNextVar, parent.getANDState().getIdentifiers().size() - 1) : sNextVar; // For nested replicated components within replicated components
            		return sNextVar;
            	}
            }
            else if (expr.toString().equals(var)) {
            	DashHelper.setVarFound(true);
            	if (current.isCreatingSnapshot) {
            		return DashHelper.createExprVar(qualifiedVarName);
            	}
            	if (current.isCreatingEnabledAfterPred && isEnvVar) {
            		return DashHelper.createExprBadJoin(DashHelper._s(), qualifiedVarName);
            	}
            	else if (current.isCreatingEnabledAfterPred && DashOptions.isElectrum && !isRef) {
        			Expr variable = DashHelper.createExprVar(qualifiedVarName);
        			Expr sVarPrimed = DashHelper.sVarPrimed(variable);
        			sVarPrimed = DashHelper.addParametersJoin(sVarPrimed, parent.getANDState().getIdentifiers().size());
        			return sVarPrimed;
            	}
             	else {
            		if (!isRef && (current.isCreatingInit) && (!current.isCreatingExprQt) && parent.getANDState().getIdentifiers().size() > 0) {
            			Expr variable = DashHelper.createExprVar(qualifiedVarName);
	                	Expr sVar =  DashHelper.createBinaryExpr(DashHelper.s(), ExprBinary.Op.JOIN, variable);
	                	Expr idSVar = DashHelper.createBinaryExpr(DashHelper.createExprVar("p" + module.getIdentifierElements().indexOf(parent.getANDState().getReplicatedIdentifier())), ExprBinary.Op.JOIN, sVar); //DashHelper.addParametersJoin(sVar, parent.getIdentifiers().size());;
	                	return idSVar;
            		}
            		else if (!isRef && !(current.isCreatingInit && current.isCreatingExprQt)) { // No need to DotJoin the "p0" expr if it is a reference to another parameterized concurrent state
            			Expr variable = DashHelper.createExprVar(qualifiedVarName);
	                	Expr sVar =  DashHelper.createBinaryExpr(DashHelper.s(), ExprBinary.Op.JOIN, variable);
	                	sVar= DashHelper.addParametersJoin(sVar, parent.getANDState().getIdentifiers().size());
	                	return sVar;
                	}
                	else {
                		Expr sVar = DashHelper.createExprBadJoin(DashHelper.s(), DashHelper.createExprVar(qualifiedVarName));
                		Expr p0SVar = parent.getANDState().getIdentifiers() != null ? DashHelper.addParametersJoin(sVar, parent.getANDState().getIdentifiers().size() - 1) : sVar; // For nested replicated components within replicated components
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
        	 current.foundBuffer = (current.bufferCommands.contains(right.toString()) && module.getBuffers().containsKey(joinLeftRightRight.toString())) ? true : false;
        	 if (current.bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprVar)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
            	 //System.out.println("Join Left: " + joinLeft + " joinLeftRight: " + joinLeftRight);
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && current.bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing1: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 current.paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 current.changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 current.paramBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 } 
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: (p.bufferName).remove [a buffer call with no parameters such as remove]
        	 if (current.bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBinary && joinLeft.left instanceof ExprVar)) {
        		 ExprBinary joinLeftRight = (ExprBinary) joinLeft.right;
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && current.bufferCommands.contains(right.toString())) {
        			 //System.out.println("ChangingBuffer2: " + joinLeftRight.right.toString() + " Left: " + joinLeft + " Command: " + right.toString());
        			 current.paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 current.changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 current.changedLocalVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 current.localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        	 // Handles cases in which a parametererized conc state makes the following call: ConcState[buffer1.first]/buffer0.add[pid]
        	 if (current.bufferCommands.contains(right.toString()) && (joinLeft.right instanceof ExprBadJoin && joinLeft.left instanceof ExprBadJoin)) {
        		 ExprBadJoin joinLeftRight = (ExprBadJoin) joinLeft.right;
        		 if (module.getBuffers().containsKey(joinLeftRight.right.toString()) && current.bufferCommands.contains(right.toString())) {
        			 //System.out.println("Changing3: " + joinLeftRight.right.toString() + " Left: " + joinLeft.left + " Command: " + right.toString());
        			 current.paramBuffer.put(joinLeftRight.right.toString(), joinLeft.left);
        			 current.changedVars.put(joinLeftRight.right.toString(), module.getBuffers().get(joinLeftRight.right.toString()));
        			 if (module.getBuffers().get(joinLeftRight.right.toString()).isParameterized()) {
        				 current.localBufferChanged.put(joinLeftRight.right.toString(), joinLeft.left);
        			 }
        		 }
        	 }
        }
        if (current.foundBuffer && joinLeft != null) {
        	current.changedVars.put(joinLeft.right.toString(), parent);
        }
    }
    
    Expr breakdownBufferCall (ExprBadJoin joinLeft, DashConcState parent) {
    	for (int i = 0; i < parent.getIdentifiers().size() - 1; i++) {
    		if (joinLeft.right instanceof ExprBadJoin) {
    			joinLeft = (ExprBadJoin) joinLeft.right;
    		}
    	}
    	return joinLeft;
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
    
    
    /*************************** HELPER FUNCTIONS ******************************/
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
}
