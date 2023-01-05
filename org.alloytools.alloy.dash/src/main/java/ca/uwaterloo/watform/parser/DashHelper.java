package ca.uwaterloo.watform.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashEvent;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashSuperState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprBinary.Op;

public class DashHelper {
	
	public static enum ItemType {
		ANDSTATE,
		ORSTATE,
		VAR,
		EVENT,
		TRANS,
		INIT,
		INVAR
	}

	public static String toLowerCase(String string) {
		return Character.toLowerCase(string.charAt(0)) + string.substring(1);
	}
	
	public static String toUpperCase(String string) {
		return Character.toUpperCase(string.charAt(0)) + string.substring(1);
	}
	
	public static String cleanVariable(String variable) {
		return variable.endsWith("'") ? variable.substring(0, variable.length() - 1) : variable;
	}
	
	public static Expr parameterize(String string) {
		return createBinaryExpr(createExprVar("p"), ExprBinary.Op.JOIN ,createExprVar(DashHelper.toLowerCase(string)));
	}
	
	private static boolean varFound;
	
	public static boolean varFound() {
		return varFound;
	}
	
	public static void setVarFound(boolean found) {
		varFound = found;
	}
		 
	/*
	 * If a Snapshot variable (assume a variable: var) originates from a Parameterized Concurrent State (assume with a parameter called p), then we create the following:
	 * var: p -> expr
	 */
	public static Expr createParameterizedVar(String var, Expr expr, DashModule module) {
		DashConcState concState = module.getVariableConcState().get(var).getANDState();
		/*
		if(module.getVariableConcState().containsKey(var)) {
			System.out.println("The Key is Present");
		} else {
			System.out.println("No key");
		}
		if (module.getVariableConcState().get(var) == null) {
			System.out.println("Get is null");
		} else {
			System.out.println("Parent: " + module.getVariableConcState().get(var).getFullyQualName());
		}
		if (module.getVariableConcState().get(var).getANDState() == null) {
			System.out.println("Get is null");
		}
		*/
		if (expr instanceof ExprUnary && concState.getIdentifiers().size() > 0) {
			ExprUnary exprUnary = (ExprUnary) expr;	
			int index = concState.getIdentifiers().size() - 1;
			if (exprUnary.op == ExprUnary.Op.LONEOF)
				expr = ExprBinary.Op.ANY_ARROW_LONE.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.ONEOF)
				expr = ExprBinary.Op.ANY_ARROW_ONE.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SOMEOF)
				expr = ExprBinary.Op.ANY_ARROW_SOME.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SETOF)
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			for (int i = concState.getIdentifiers().size() - 2; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		} 
		else if (expr instanceof ExprVar) {
			for (int i = concState.getIdentifiers().size() - 1; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		}
		else if (expr instanceof ExprBinary) {
			for (int i = concState.getIdentifiers().size() - 1; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		}
		return expr;
	} 
	
	public static Expr createParameterizedElectrumVar(String var, Expr expr, DashModule module) {
		DashConcState concState = module.getVariableConcState().get(var).getANDState();
		if (expr instanceof ExprUnary && concState.getIdentifiers().size() > 1) {
			ExprUnary exprUnary = (ExprUnary) expr;	
			int index = concState.getIdentifiers().size() - 1;
			if (exprUnary.op == ExprUnary.Op.LONEOF)
				expr = ExprBinary.Op.ANY_ARROW_LONE.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.ONEOF)
				expr = ExprBinary.Op.ANY_ARROW_ONE.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SOMEOF)
				expr = ExprBinary.Op.ANY_ARROW_SOME.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SETOF)
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(index)), exprUnary.sub);
			for (int i = concState.getIdentifiers().size() - 3; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		} 
		else if (expr instanceof ExprVar) {
			for (int i = concState.getIdentifiers().size() - 2; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		}
		else if (expr instanceof ExprBinary) {
			for (int i = concState.getIdentifiers().size() - 2; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), expr);
			}
		}
		return expr;
	}
	
	public static Expr createParameterizedExpr(String var, DashConcState concState) {
		Expr returnExpr = ExprVar.make(null, var);
		for (int i = concState.getIdentifiers().size() - 1; i >= 0; i--) {
			returnExpr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.getIdentifiers().get(i)), returnExpr);
		}

		return returnExpr;
	}
	
	public static Expr addParametersJoin (Expr expr, int totalIEs) {
        for (int i = 0; i < totalIEs; i++) {
        	expr = ExprBadJoin.make(null, null, createExprVar("p" + i), expr);
        }
        return expr;
	}
	
	public static Expr addIdentifiersJoin (Expr expr, List<String> identifiers, boolean ignoreFirst) {
        for (int i = 0; i < identifiers.size(); i++) {
        	if (ignoreFirst && i == 0) continue;
        	expr = ExprBadJoin.make(null, null, createExprVar(identifiers.get(i)), expr);
        }
        return expr;
	}
	
	public static Expr addParametersArrow (Expr expr, DashConcState concState) {
		for (int i = concState.getIdentifiers().size() - 1; i >= 0; i--) {
			expr = ExprBinary.Op.ARROW.make(null, null, createExprVar("p" + i), expr);
		}
		return expr;
	}
	
	public static Expr addParametersArrow (Expr expr, int ies) {
		for (int i = ies - 1; i >= 0; i--) {
			expr = ExprBinary.Op.ARROW.make(null, null, createExprVar("p" + i), expr);
		}
		return expr;
	}
	
	public static Expr addIdentifiersArrow (Expr expr, int ies) {
		for (int i = 0; i < ies; i++) {
			expr = ExprBinary.Op.ARROW.make(null, null, createExprVar("Identifiers"), expr);
		}
		return expr;
	}
	
	public static Expr addIdentifiersNone (Expr expr, int ies) {
		for (int i = 0; i < ies; i++) {
			expr = ExprBinary.Op.ARROW.make(null, null, createExprVar("none"), expr);
		}
		return expr;
	}
	
	public static Expr quantify (DashConcState parent, Expr expr) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        //expr = DashHelper.addParametersJoin(expr, parent.getIdentifiers().size());
        for (int i = 0; i < parent.getIdentifiers().size(); i++) { 
            a.add(ExprVar.make(null, "p" + i));
            decls.add(new Decl(null, null, null, null, a, ExprVar.make(null, parent.getIdentifiers().get(i))));
            a.clear();
        }
        return ExprQt.Op.ALL.make(null, null, decls, expr);
	}
	
	public static Expr noTakenSemanticsConstraints(String type, int taken, DashModule module) {
		Expr equals = null;
		for (int key: module.getConfLevels()) {
			if (key == taken) {
				continue;
			}
			Expr sNextTaken = DashOptions.isElectrum ? sVarPrimed(type + key) : sNextVar(type + key);
			Expr noSNextTaken = createUnaryExpr(ExprUnary.Op.NO, sNextTaken);
			equals = equals == null ? noSNextTaken : createBinaryExpr(equals, ExprBinary.Op.AND, noSNextTaken);
		}
		return equals;
	}
	
	public static Expr constraintEquals(String type, int conf, DashModule module) {
		Expr equals = null;
		for (int key: module.getConfLevels()) {
			if (key == conf) {
				continue;
			}
			Expr sRight = createBinaryExpr(s(), ExprBinary.Op.JOIN, createExprVar(type + key)); 
			Expr sNextLeft = DashOptions.isElectrum ? sVarPrimed(type + key) : sNextVar(type + key);
			Expr equal = createBinaryExpr(sNextLeft, ExprBinary.Op.EQUALS, sRight);
			equals = equals == null ? equal : createBinaryExpr(equals, ExprBinary.Op.AND, equal);
		}
		return equals;
	}
	
	public static Expr constraintConf (int conf, DashModule module) {
		Expr equals = null;
		for (int key: module.getConfLevels()) {
			if (key == conf) {
				continue;
			}
			Expr equal = ExprBinary.Op.EQUALS.make(null, null, sNextConf(key), sConf(key));
			equals = equals == null ? equal : ExprBinary.Op.AND.make(null, null, equals, equal);
		}
		return equals;
	}
	
	public static List<DashConcState> getNestedConcStates (DashConcState concState) {
		List<DashConcState> innerConcStates = new ArrayList<DashConcState>();
		if (concState.getInnerConcStates().size() > 0) {
			return concState.getInnerConcStates();
		}
		if (concState.getInnerORStates().size() > 0) {
			for (DashState innerState: concState.getInnerORStates()) {
				getConcurrentStateInORState(innerState, innerConcStates);
			}
		}
		return innerConcStates;
	}
	
	public static List<DashSuperState> getNestedStates (DashSuperState state) {
		List<DashSuperState> nestedStates = new ArrayList<>();
		nestedStates.add(state);
		state.getInnerConcStates().forEach(x -> {
			nestedStates.add(x);
			getNestedStatesHelper(x, nestedStates);
		});
		state.getInnerORStates().forEach(x -> {
			nestedStates.add(x);
			getNestedStatesHelper(x, nestedStates);
		});
		return nestedStates;
	}
	
	public static void getNestedStatesHelper(DashSuperState state, List<DashSuperState> states) {
		state.getInnerConcStates().forEach(x -> {
			states.add(x);
			getNestedStatesHelper(x, states);
		});
		state.getInnerORStates().forEach(x -> {
			states.add(x);
			getNestedStatesHelper(x, states);
		});
	}
	
	public static void getConcurrentStateInORState(DashState state, List<DashConcState> concStates) {
		if (state.getInnerConcStates().size() > 0) {
			concStates.addAll(state.getInnerConcStates());
		}
		if(state.getInnerORStates().size() > 0) {
			for (DashState innerState: state.getInnerORStates()) {
				getConcurrentStateInORState(innerState, concStates);
			}
		}
	}
	
    public static DashConcState getConcStateReferred (Expr ref, DashConcState parent) {
    	String reference = ExprVar.make(null, ref.toString()).toString();
    	List<String> refNames = new ArrayList<String>();
    	while ((reference.indexOf("/") > -1)) {
    		String stateRef = reference.toString().substring(0, reference.toString().indexOf("/"));
    		if (parent.getRawName() == stateRef) {
    			return parent;
    		}
    		refNames.add(stateRef);
    		reference = reference.substring(reference.indexOf("/") + 1);
    	}
    	
    	Object child = parent;
    	for (String refName: refNames) {
    		if (child instanceof DashConcState) {
    			DashConcState concState = (DashConcState) child;
    			for (DashConcState inner: concState.getInnerConcStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    			for (DashState inner: concState.getInnerORStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    		}
    		
    		if (child instanceof DashState) {
    			DashState state = (DashState) child;
    			for (DashConcState inner: state.getInnerConcStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    			for (DashState inner: state.getInnerORStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    		}
    	}
    	
    	if (child instanceof DashConcState) {
    		return (DashConcState) child;
    	}
    	else {
    		return null;
    	}
    }
    
    public static DashConcState getConcStateReferred (String ref, DashConcState parent) {
    	String reference = ExprVar.make(null, ref.toString()).toString();
    	List<String> refNames = new ArrayList<String>();
    	while ((reference.indexOf("/") > -1)) {
    		String stateRef = reference.toString().substring(0, reference.toString().indexOf("/"));
    		refNames.add(stateRef);
    		reference = reference.substring(reference.indexOf("/") + 1);
    	}
    	
    	Object child = parent;
    	for (String refName: refNames) {
    		if (child instanceof DashConcState) {
    			DashConcState concState = (DashConcState) child;
    			for (DashConcState inner: concState.getInnerConcStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    			for (DashState inner: concState.getInnerORStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    		}
    		
    		if (child instanceof DashState) {
    			DashState state = (DashState) child;
    			for (DashConcState inner: state.getInnerConcStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    			for (DashState inner: state.getInnerORStates()) {
    				if (inner.getRawName().equals(refName))
    					child = inner;
    			}
    		}
    	}
    	
    	if (child instanceof DashConcState) {
    		return (DashConcState) child;
    	}
    	else {
    		return null;
    	}
    }
	
	public static Map<Integer, Expr> calculateConf2GotoExpr(DashTrans transition) {
		Map<Integer, Expr> conf2GotoExpr = new LinkedHashMap<Integer, Expr>();
		// For each Destination state
    	for (String key: transition.getDestination().getDefaultStatesEntered().keySet()) {
    		// Create DestState expression
    		Expr destState = ExprVar.make(null, key);
    		// Get the parent concurrent state of the Destination state
    		DashConcState destStateParent = transition.getDestination().getDefaultStatesEntered().get(key);
    		// Get the number of identifiers that maps to the state
    		int ieSize = destStateParent.getIdentifiers().size();
    		// Create the following (IE -> IE -> State)
            for (int i = ieSize - 1; i >= 0; i--) {
            	// p0 enters a state with concurrent states
            	if (i < transition.getParentConcState().getIdentifiers().size()) {
            		destState = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), destState);
            	}
            	else {
            		destState = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, destStateParent.getIdentifiers().get(i)), destState);
            	}
            }
            
            if (!conf2GotoExpr.containsKey(ieSize)) {
            	conf2GotoExpr.put(ieSize, destState);
            } else {
            	// Create: (IE -> State) + (IE -> State)
            	Expr expr = ExprBinary.Op.PLUS.make(null, null, conf2GotoExpr.get(ieSize), destState);
            	conf2GotoExpr.put(ieSize, expr);
            }
    	}
		
		return conf2GotoExpr;
	}
	

	public static Map<Integer, Expr> calculateConf2FromExpr(DashTrans transition) {
		Map<Integer, Expr> conf2FromExpr = new LinkedHashMap<Integer, Expr>();
		// For each Source state
    	for (DashConcState key: transition.getOrigin().getConcStatesExited()) {
    		// Create SourceStste expression
    		Expr parentStateExited = ExprVar.make(null, transition.getOrigin().getStateBeingLeft());
    		int ieSize = key.getIdentifiers().size();
    		// Create the following (IE -> IE -> State)
            for (int i = key.getIdentifiers().size() - 1; i >= 0; i--) {
            	if (i < transition.getParentConcState().getIdentifiers().size()) {
            		parentStateExited = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), parentStateExited);
            	}
            	else {
            		parentStateExited = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, key.getIdentifiers().get(i)), parentStateExited);
            	}
            }
            conf2FromExpr.put(ieSize, parentStateExited);
    	}
		
		return conf2FromExpr;
	}
	
    public static DashState getState(String stateName, DashModule module) {
    	return module.getORStates().get(stateName);
   }
	
    /*************************** CREATING EXPRESSIONS ******************************/
	
	public static Expr createExprVar(String expr) {
		return ExprVar.make(null, expr);
	}
	
	public static Expr createExprBadJoin(String left, String right) {
		return ExprBadJoin.make(null, null, createExprVar(left), createExprVar(right)); 
	}
	
	public static Expr createExprBadJoin(String left, Expr right) {
		return ExprBadJoin.make(null, null, createExprVar(left), right); 
	}
	
	public static Expr createExprBadJoin(Expr left, String right) {
		return ExprBadJoin.make(null, null, left, createExprVar(right)); 
	}
	
	public static Expr createExprBadJoin(Expr left, Expr right) {
		return ExprBadJoin.make(null, null, left, right); 
	}
	
    public static Expr createBinaryExpr(Expr left, ExprBinary.Op op, Expr right) {
        if(op == Op.ARROW)
        	return (ExprBinary) ExprBinary.Op.ARROW.make(null, null, left, right);
        if(op == Op.JOIN)
        	return (ExprBinary) ExprBinary.Op.JOIN.make(null, null, left, right);
        if(op == Op.DOMAIN)
        	return (ExprBinary) ExprBinary.Op.DOMAIN.make(null, null, left, right);
        if(op == Op.RANGE)
        	return (ExprBinary) ExprBinary.Op.RANGE.make(null, null, left, right);
        if(op == Op.INTERSECT)
        	return (ExprBinary) ExprBinary.Op.INTERSECT.make(null, null, left, right);
        if(op == Op.PLUSPLUS)
        	return (ExprBinary) ExprBinary.Op.PLUSPLUS.make(null, null, left, right);
        if(op == Op.PLUSPLUS)
        	return (ExprBinary) ExprBinary.Op.PLUSPLUS.make(null, null, left, right);
        if(op == Op.PLUS)
        	return (ExprBinary) ExprBinary.Op.PLUS.make(null, null, left, right);
        if(op == Op.MINUS)
        	return (ExprBinary) ExprBinary.Op.MINUS.make(null, null, left, right);
        if(op == Op.MUL)
        	return (ExprBinary) ExprBinary.Op.MUL.make(null, null, left, right);
        if(op == Op.DIV)
        	return (ExprBinary) ExprBinary.Op.DIV.make(null, null, left, right);
        if(op == Op.REM)
        	return (ExprBinary) ExprBinary.Op.REM.make(null, null, left, right);
        if(op == Op.EQUALS)
        	return (ExprBinary) ExprBinary.Op.EQUALS.make(null, null, left, right);
        if(op == Op.NOT_EQUALS)
        	return (ExprBinary) ExprBinary.Op.NOT_EQUALS.make(null, null, left, right);
        if(op == Op.IMPLIES)
        	return (ExprBinary) ExprBinary.Op.IMPLIES.make(null, null, left, right);
        if(op == Op.LT)
        	return (ExprBinary) ExprBinary.Op.LT.make(null, null, left, right);
        if(op == Op.LTE)
        	return (ExprBinary) ExprBinary.Op.LTE.make(null, null, left, right);
        if(op == Op.GT)
        	return (ExprBinary) ExprBinary.Op.GT.make(null, null, left, right);
        if(op == Op.GTE)
        	return (ExprBinary) ExprBinary.Op.GTE.make(null, null, left, right);
        if(op == Op.NOT_LT)
        	return (ExprBinary) ExprBinary.Op.NOT_LT.make(null, null, left, right);
        if(op == Op.NOT_LTE)
        	return (ExprBinary) ExprBinary.Op.NOT_LTE.make(null, null, left, right);
        if(op == Op.NOT_GT)
        	return (ExprBinary) ExprBinary.Op.NOT_GT.make(null, null, left, right);
        if(op == Op.NOT_GTE)
        	return (ExprBinary) ExprBinary.Op.NOT_GTE.make(null, null, left, right);
        if(op == Op.SHL)
        	return (ExprBinary) ExprBinary.Op.SHL.make(null, null, left, right);
        if(op == Op.SHA)
        	return (ExprBinary) ExprBinary.Op.SHA.make(null, null, left, right);
        if(op == Op.SHR)
        	return (ExprBinary) ExprBinary.Op.SHR.make(null, null, left, right);
        if(op == Op.IN)
        	return (ExprBinary) ExprBinary.Op.IN.make(null, null, left, right);
        if(op == Op.NOT_IN)
        	return (ExprBinary) ExprBinary.Op.NOT_IN.make(null, null, left, right);
        if(op == Op.AND)
        	return ExprBinary.Op.AND.make(null, null, left, right);
        if(op == Op.OR)
        	return ExprBinary.Op.OR.make(null, null, left, right);
        if(op == Op.IFF)
        	return (ExprBinary) ExprBinary.Op.IFF.make(null, null, left, right);
        if(op == Op.UNTIL)
        	return (ExprBinary) ExprBinary.Op.UNTIL.make(null, null, left, right);
        if(op == Op.RELEASES)
        	return (ExprBinary) ExprBinary.Op.RELEASES.make(null, null, left, right);
        if(op == Op.SINCE)
        	return (ExprBinary) ExprBinary.Op.SINCE.make(null, null, left, right);
        if(op == Op.TRIGGERED)
        	return (ExprBinary) ExprBinary.Op.TRIGGERED.make(null, null, left, right);
        if(op == Op.ISSEQ_ARROW_LONE)
        	return ExprBinary.Op.ISSEQ_ARROW_LONE.make(null, null, left, right);
        if(op == Op.ONE_ARROW_ONE) 
            return ExprBinary.Op.ONE_ARROW_ONE.make(null, null, left, right);
        
        return null;
    }
    
    public static ExprUnary createUnaryExpr(ExprUnary.Op op, Expr sub) {
        if(op == ExprUnary.Op.SOMEOF)
        	return (ExprUnary) ExprUnary.Op.SOMEOF.make(null, sub);
        if(op == ExprUnary.Op.LONEOF)
        	return (ExprUnary) ExprUnary.Op.LONEOF.make(null, sub);
        if(op == ExprUnary.Op.ONEOF)
        	return (ExprUnary) ExprUnary.Op.ONEOF.make(null, sub);
        if(op == ExprUnary.Op.SETOF)
        	return (ExprUnary) ExprUnary.Op.SETOF.make(null, sub);
        if(op == ExprUnary.Op.EXACTLYOF)
        	return (ExprUnary) ExprUnary.Op.EXACTLYOF.make(null, sub);
        if(op == ExprUnary.Op.NOT)
        	return (ExprUnary) ExprUnary.Op.NOT.make(null, sub);
        if(op == ExprUnary.Op.NO)
        	return (ExprUnary) ExprUnary.Op.NO.make(null, sub);
        if(op == ExprUnary.Op.SOME)
        	return (ExprUnary) ExprUnary.Op.SOME.make(null, sub);
        if(op == ExprUnary.Op.LONE)
        	return (ExprUnary) ExprUnary.Op.LONE.make(null, sub);
        if(op == ExprUnary.Op.ONE)
        	return (ExprUnary) ExprUnary.Op.ONE.make(null, sub);
        if(op == ExprUnary.Op.TRANSPOSE)
        	return (ExprUnary) ExprUnary.Op.TRANSPOSE.make(null, sub);
        if(op == ExprUnary.Op.PRIME)
        	return (ExprUnary) ExprUnary.Op.PRIME.make(null, sub);
        if(op == ExprUnary.Op.RCLOSURE)
        	return (ExprUnary) ExprUnary.Op.RCLOSURE.make(null, sub);
        if(op == ExprUnary.Op.CLOSURE)
        	return (ExprUnary) ExprUnary.Op.CLOSURE.make(null, sub);
        if(op == ExprUnary.Op.CARDINALITY)
        	return (ExprUnary) ExprUnary.Op.CARDINALITY.make(null, sub);
        if(op == ExprUnary.Op.CAST2INT)
        	return (ExprUnary) ExprUnary.Op.CAST2INT.make(null, sub);
        if(op == ExprUnary.Op.CAST2SIGINT)
        	return (ExprUnary) ExprUnary.Op.CAST2SIGINT.make(null, sub);
        if(op == ExprUnary.Op.NOOP)
        	return (ExprUnary) ExprUnary.Op.NOOP.make(null, sub);
        if(op == ExprUnary.Op.ALWAYS)
        	return (ExprUnary) ExprUnary.Op.ALWAYS.make(null, sub);
        if(op == ExprUnary.Op.EVENTUALLY)
        	return (ExprUnary) ExprUnary.Op.EVENTUALLY.make(null, sub);
            
        return null;
    }
    
    public static ExprList createExprList(ExprList.Op op, List<Expr> args) {
        if(op == ExprList.Op.DISJOINT)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.DISJOINT, args);
        if(op == ExprList.Op.TOTALORDER)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.TOTALORDER, args);
        if(op == ExprList.Op.AND)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.AND, args);
        if(op == ExprList.Op.OR)
        	return (ExprList) ExprList.make(null, null, ExprList.Op.OR, args);
   
        return null;
    }
    
    public static ExprQt createExprQt(ExprQt.Op op, List<Decl> decls, Expr expr) {
        if(op == ExprQt.Op.ALL)
        	return (ExprQt) ExprQt.Op.ALL.make(null, null, decls, expr);
        if(op == ExprQt.Op.NO)
        	return (ExprQt) ExprQt.Op.NO.make(null, null, decls, expr);
        if(op == ExprQt.Op.LONE)
        	return (ExprQt) ExprQt.Op.LONE.make(null, null, decls, expr);
        if(op == ExprQt.Op.ONE)
        	return (ExprQt) ExprQt.Op.ONE.make(null, null, decls, expr);
        if(op == ExprQt.Op.SOME)
        	return (ExprQt) ExprQt.Op.SOME.make(null, null, decls, expr);
        if(op == ExprQt.Op.SUM)
        	return (ExprQt) ExprQt.Op.SUM.make(null, null, decls, expr);
        if(op == ExprQt.Op.COMPREHENSION)
        	return (ExprQt) ExprQt.Op.COMPREHENSION.make(null, null, decls, expr);
   
        return null;
    }
    
    public static ExprITE createImplesElseExpr(Expr cond, Expr impliesExpr, Expr elseExpr) {
    	return (ExprITE) ExprITE.make(null, cond, impliesExpr, elseExpr);
    }
    
    /************************************ PRE-DEFINED EXPRESSIONS *****************************************/
    
    public static Expr s() {
    	return ExprVar.make(null, "s");
    }
    
    public static Expr _s() {
    	return ExprVar.make(null, "_s");
    }
    
    public static Expr sNext() {
    	return ExprVar.make(null, "s_next");
    }
    
    public static Expr sPrimed() {
    	return createUnaryExpr(ExprUnary.Op.PRIME, s());
    }
    
    public static Expr conf(int i) {
    	return ExprVar.make(null, "conf" + i);
    }
    
    public static Expr conf() {
    	return ExprVar.make(null, "conf");
    }
    
    public static Expr events(int i) {
    	return ExprVar.make(null, "events" + i);
    }
    
    public static Expr taken(int i) {
    	return ExprVar.make(null, "taken" + i);
    }
    
    public static Expr stable() {
    	return ExprVar.make(null, "stable");
    }
    
    public static Expr intEvent() {
    	return ExprVar.make(null, "InternalEvent");
    }
    
    public static Expr envEvent() {
    	return ExprVar.make(null, "EnvironmentEvent");
    }
    
    public static Expr sConf(int i) {
    	return createExprBadJoin(s(), conf(i));
    }
    
    public static Expr sConf () {
    	return createExprBadJoin(s(), conf());
    }
    
    public static Expr sNextConf(int i) {
    	return createExprBadJoin(sNext(), conf(i));
    }
    
    public static Expr sStable() {
    	return createExprBadJoin(s(), stable());
    }
    
    public static Expr _sStable() {
    	return createExprBadJoin(_s(), stable());
    }
    
    public static Expr sNextStable() {
    	return createExprBadJoin(sNext(), stable());
    }
    
    public static Expr sTaken(int i) {
    	return createExprBadJoin(s(), taken(i));
    }
    
    public static Expr _sTaken(int i) {
    	return createExprBadJoin(_s(), taken(i));
    }
    
    public static Expr sNextTaken(int i) {
    	return createExprBadJoin(sNext(), taken(i));
    }
    
    public static Expr sEvents(int i) {
    	return createExprBadJoin(s(), events(i));
    }
    
    public static Expr _sEvents(int i) {
    	return createExprBadJoin(_s(), events(i));
    }
    
    public static Expr sNextEvents(int i) {
    	return createExprBadJoin(sNext(), events(i));
    }
    
    public static Expr sVar (Expr var) {
    	return createExprBadJoin(s(), var);
    }
    
    public static Expr sNextVar (Expr var) {
    	return createExprBadJoin(sNext(), var);
    }
    
    public static Expr sNextVar (String var) {
    	return createExprBadJoin(sNext(), createExprVar(var));
    }

    public static Expr identifiers() {
    	return ExprVar.make(null, "Identifiers");
    }
    
    public static Expr variables() {
    	return ExprVar.make(null, "Variables");
    }
    
    public static Expr trueExpr() {
    	return ExprVar.make(null, "True");
    }
    
    public static Expr falseExpr() {
    	return ExprVar.make(null, "False");
    }
    
    /* ELECTRUM HELPER FUNCTIONS */
	public static Expr confPrimed(int i) {
		return ExprUnary.Op.PRIME.make(null, conf(i));
	}
	
	public static Expr eventsPrimed(int i) {
		return ExprUnary.Op.PRIME.make(null, events(i));
	}
	
	public static Expr takenPrimed(int i) {
		return ExprUnary.Op.PRIME.make(null, taken(i));
	}
	
	public static Expr stablePrimed() {
		return ExprUnary.Op.PRIME.make(null, stable());
	}
	
	public static Expr varPrimed(Expr var) {
		return ExprUnary.Op.PRIME.make(null, var);
	}
	
	public static Expr varPrimed(String var) {
		return ExprUnary.Op.PRIME.make(null, createExprVar(var));
	}	
	
	public static Expr sConfPrimed(int i) {
		Expr confPrimed = ExprUnary.Op.PRIME.make(null, conf(i));
		return createExprBadJoin("s", confPrimed);
	}
	
	public static Expr sEventsPrimed(int i) {
		Expr eventsPrimed = ExprUnary.Op.PRIME.make(null, events(i));
		return createExprBadJoin("s", eventsPrimed);
	}
	
	public static Expr sTakenPrimed(int i) {
		Expr takenPrimed = ExprUnary.Op.PRIME.make(null, taken(i));
		return createExprBadJoin("s", takenPrimed);
	}
	
	public static Expr sStablePrimed() {
		Expr stablePrimed = ExprUnary.Op.PRIME.make(null, stable());
		return createExprBadJoin("s", stablePrimed);
	}

	public static Expr sVarPrimed(Expr var) {
		Expr varPrimed = ExprUnary.Op.PRIME.make(null, var);
		return createExprBadJoin("s", varPrimed);
	}
	
	public static Expr sVarPrimed(String var) {
		Expr varPrimed = ExprUnary.Op.PRIME.make(null, createExprVar(var));
		return createExprBadJoin("s", varPrimed);
	}	

   public static Boolean checkInternalEvent(DashTrans trans, DashModule module)
   {
       if (trans.getTriggerEvent() == null)
           return false;
   	
       String onCommand = trans.getTriggerEvent().getRawName();

       if (onCommand.contains("/")) 
           onCommand = onCommand.substring(onCommand.lastIndexOf('/') + 1);

       for(DashConcState concState: module.getAllConcurrentStates().values()) {
		for(DashEvent event: concState.getEvents()) {
			if(event.getType().equals("event") && event.getRawName().equals(onCommand)) {
				return true;
			} 
		}
       }  
       return false;
   }
   
  public static void getInnerStates(DashState state, List<DashState> states) {
		for(DashState innerState: state.getInnerORStates()) {	
			states.add(innerState);
			
			if(innerState.getInnerORStates().size() > 0)
				getInnerStates(innerState, states);
		}
  }
  
  public static void getInnerANDStates(DashConcState state, List<DashConcState> states) {
		for(DashConcState innerState: state.getInnerConcStates()) {	
			states.add(innerState);
			
			if(innerState.getInnerConcStates().size() > 0)
				getInnerANDStates(innerState, states);
		}
}
   
  public static DashConcState getParentConcState(Object item) { 	
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

  public static Object getParent(Object parent) {
       if (parent instanceof DashState)
           return ((DashState) parent).getParent();
       if (parent instanceof DashConcState)
           return ((DashConcState) parent).getParent();
       return null;
   }
  
  public static DashConcState getTopLevelConcState(DashSuperState state) {
	  if (state.getParentConcState() == null) {
		  return state.getANDState(); 
	  }
	  return getTopLevelConcState(state.getParentConcState());
  }
  
  public static Optional<DashConcState> locateANDState(DashConcState concState, String name) {
	  if (concState == null) {
		  return Optional.empty();
	  }
	  if (concState.getRawName().equals(name)) {
		  return Optional.ofNullable(concState);
	  }
	  List<DashConcState> allInnerConcStates = new ArrayList<>();
	  getInnerANDStates(concState, allInnerConcStates);
	  List<DashConcState> match = allInnerConcStates.stream().filter(x -> x.getRawName().equals(name)).collect(Collectors.toCollection(ArrayList::new));
	  return match.size() == 0 ? Optional.empty() : Optional.ofNullable(match.get(0));
  }
  
  /****************************** Locate a State within an AND-state ***********************************/
  public static Optional<DashSuperState> locateState (DashConcState concState, String name) {
	  if (concState == null) {
		  return Optional.empty();
	  }
	  if (concState.getRawName().equals(name)) {
		  return Optional.ofNullable(concState);
	  }
	  List<DashSuperState> match = new ArrayList<>();
	  locateStateHelper(concState, name, match);
	  return match.size() == 0 ? Optional.empty() : Optional.ofNullable(match.get(0));
  }
   
  public static void locateStateHelper (DashSuperState state, String name, List<DashSuperState> match) {
	  if (match.size() > 0) {
		  return;
	  }
	  List<DashConcState> ANDMatches = state.getInnerConcStates().parallelStream().filter(x -> x.getRawName().equals(name)).collect(Collectors.toCollection(ArrayList::new));
	  List<DashState> ORMatches = state.getInnerORStates().parallelStream().filter(x -> x.getRawName().equals(name)).collect(Collectors.toCollection(ArrayList::new));
	  match.addAll(ANDMatches);
	  match.addAll(ORMatches);
	  state.getInnerConcStates().forEach((x) -> locateStateHelper(x, name, match));
	  state.getInnerORStates().forEach((x) -> locateStateHelper(x, name, match));
  }
  
  /*
   * Locate the parent state of an item that is being referenced (state/myVar) -> state
   */
  public static void findItemParentLocally(DashSuperState state, final String reference, List<DashSuperState> match) {
	  if (reference.indexOf('/') < 0 || match.size() > 0) {
		  return;
	  }
	  String stateName = reference.substring(0, reference.indexOf('/'));
	  if (state.getRawName().equals(stateName)) {
		  match.add(state);
	  }
	  state.getInnerConcStates().forEach((x) -> findItemParentLocally(x, reference, match));
	  state.getInnerORStates().forEach((x) -> findItemParentLocally(x, reference, match));
  }
  
  /* 
   * Locate the parent state of an item that is being referenced (state/myVar) -> 
   * (state = parent state), (myVar = item being referenced)
   * Start by checking if the variable is present inside the AND-state in which it was declared
   * If not, perform a search of all AND-states to look for the variable
   */
  public static Optional<DashSuperState> findVariableParentByReference (DashModule module, DashConcState parent, String reference) {
	  if (reference == null || reference.indexOf('/') < 0) {
		  return Optional.empty();
	  }
	  
	  // Find the states that match name of the state we are looking for
	  List<DashSuperState> match = new ArrayList<>();
	  String stateName = reference.substring(0, reference.indexOf('/'));
	  if (parent.getRawName().equals(stateName)) {
		  match.add(parent);
	  }
	  findItemParentLocally(parent, reference, match);
	  // Search globally for the variable too
	  module.getTopLevelConcStates().values().forEach(x -> findItemParentLocally(x, reference, match));

	  ArrayList<Optional<DashSuperState>> varMatches = new ArrayList<>();
	  match.forEach(x -> varMatches.add(locateItem (module, reference.substring(reference.indexOf('/') + 1), x, DashHelper.ItemType.VAR)));

	  for (Optional<DashSuperState> state: varMatches) {
		  if (state.isPresent()) {
			  return state;
		  }
	  }
	  
	  return Optional.empty();
  }
  
  public static List<String> getVariables (DashModule module, DashSuperState state) {
	  List<String> vars = new ArrayList<String>(module.getRawVarNames().getOrDefault(state.getFullyQualName(), new ArrayList<>()));
	  List<String> envVars = new ArrayList<String>(module.getEnvironmentalVarNames().getOrDefault(state.getFullyQualName(), new ArrayList<>()));
	  vars.addAll(envVars);
	  return vars;
  }
  
  public static Optional<DashSuperState> findEventParent (DashSuperState parent, String reference) {
	  if (reference == null) {
		  return Optional.empty();
	  }
	  List<DashSuperState> match = new ArrayList<>();
	  // Look at the parent state (and child states) of the event and see if it contains the event
	  findEventParentHelper(parent, reference, match);
	  // Look at the top level AND-state for the parent
	  if (match.size() == 0) {
		  findEventParentHelper(DashHelper.getTopLevelConcState(parent), reference, match);
	  }
	  
	  return match.size() > 0 ? Optional.ofNullable(match.get(0)) : Optional.empty();
  }
  
  public static void findEventParentHelper (DashSuperState parent, String reference, List<DashSuperState> match) {
	  if (reference == null || parent == null || match == null) {
		  return;
	  }

	  if (parent.getEventNames().contains(reference)) {
		  match.add(parent);
	  }
	  parent.getInnerConcStates().forEach(x -> findEventParentHelper(x, reference, match));
	  parent.getInnerORStates().forEach(x -> findEventParentHelper(x, reference, match));
  }
  
  /* 
   * Locate an item that is being referenced 
   */
  public static Optional<DashSuperState> locateItem (DashModule module, String reference, DashSuperState match, DashHelper.ItemType itemType) {
	  if (reference.indexOf('/') < 0) {
		  return locateItemHelper(module, reference, match, itemType);
	  }
	  
	  String stateName = reference.substring(0, reference.indexOf('/'));
	  List<DashConcState> ANDMatches = match.getInnerConcStates().stream().filter(x -> x.getRawName().equals(stateName)).collect(Collectors.toCollection(ArrayList::new));
	  List<DashState> ORMatches = match.getInnerORStates().stream().filter(x -> x.getRawName().equals(stateName)).collect(Collectors.toCollection(ArrayList::new));
	  
	  if (ANDMatches.size() > 0) {
		  return locateItem(module, reference.substring(reference.indexOf('/') + 1), ANDMatches.get(0),itemType);
	  } else if (ORMatches.size() > 0) {
		  return locateItem(module, reference.substring(reference.indexOf('/') + 1), ORMatches.get(0), itemType);
	  } else {
		  return Optional.empty();
	  }
  }
  
  /*
   * Once we have broken down the reference to the last item, locate it and return its parent
   */
  public static Optional<DashSuperState> locateItemHelper (DashModule module, String reference, DashSuperState match, DashHelper.ItemType itemType) {
	  List<DashConcState> ANDMatches = match.getInnerConcStates().stream().filter(x -> x.getRawName().equals(reference)).collect(Collectors.toCollection(ArrayList::new));
	  List<DashState> ORMatches = match.getInnerORStates().stream().filter(x -> x.getRawName().equals(reference)).collect(Collectors.toCollection(ArrayList::new));
	  switch (itemType) {
		  case VAR : {
			  String variable = (reference.contains("'")) ? reference.substring(0, reference.length() - 1) : reference;
			  boolean foundMatch = (module.getRawVarNames().getOrDefault(match.getFullyQualName(), new ArrayList<>()).contains(variable))
					  || (module.getEnvironmentalVarNames().getOrDefault(match.getFullyQualName(), new ArrayList<>()).contains(variable));
			  return (foundMatch) ? Optional.ofNullable(match) : Optional.empty();
		  }
		  case ORSTATE : {
			  ANDMatches = match.getInnerConcStates().stream().filter(x -> x.getRawName().equals(reference)).collect(Collectors.toCollection(ArrayList::new));
			  ORMatches = match.getInnerORStates().stream().filter(x -> x.getRawName().equals(reference)).collect(Collectors.toCollection(ArrayList::new));
			  break;
		  }
		  case EVENT: {
			  ANDMatches = match.getInnerConcStates().stream().filter(x -> x.getEventNames().contains(reference)).collect(Collectors.toCollection(ArrayList::new));
			  ORMatches = match.getInnerORStates().stream().filter(x -> x.getEventNames().contains(reference)).collect(Collectors.toCollection(ArrayList::new));
			  break;
		  }
		  default: return Optional.empty();
	  }
	  
	  if (ANDMatches.size() > 0) {
		  return Optional.ofNullable(ANDMatches.get(0));
	  } else if (ORMatches.size() > 0) {
		  return Optional.ofNullable(ORMatches.get(0));
	  } else {
		  return Optional.empty();
	  }
  }
  
  public static Optional<DashSuperState> findVariableParent(DashModule module, DashSuperState state, String variable) {
	  if (state == null) {
		  return Optional.empty();
	  }
	  variable = DashHelper.cleanVariable(variable);
	  if (state.getVariableNames().contains(variable)) {
		  return Optional.ofNullable(state);
	  }
	  
	  List<DashSuperState> matches = new ArrayList<>();
	  findVariableParentHelper(module, getTopLevelConcState(state), variable, matches);
	  
	  return (matches.size() == 0) ? Optional.empty() : Optional.ofNullable(matches.get(0));
  }
  
  public static void findVariableParentHelper (DashModule module, DashSuperState state, String variable, List<DashSuperState> matches) {
	  if (matches.size() > 0) {
		  return;
	  }
	  if (state.getVariableNames().contains(variable)) {
		  matches.add(state);
	  }
	  state.getInnerStatesDeepCopy().forEach(nestedState -> {
		  findVariableParentHelper(module, nestedState, variable, matches);
	  });
  }
  
  /* Get all the transitions within a state */
  public static void getInnerTransitions(DashState state, List<DashTrans> transitions) {
  	for(DashTrans trans: state.getTransitions()) {
  		transitions.add(trans);
  	}
  	
  	for(DashState innerState: state.getInnerORStates()) {
  		getInnerTransitions(innerState, transitions);
  	}
  }
  
  public static String calculateStateNameWithoutConcState(DashState state) {
  	StringBuilder name = new StringBuilder();
  	DashSuperState current = state;
  	while (current != null && current instanceof DashState) {
  		name.append(state.getRawName() + '_');
  		current = (DashSuperState) state.getParent();
  	}
  	return name.toString();
  }
}
