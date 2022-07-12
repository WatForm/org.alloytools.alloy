package ca.uwaterloo.watform.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprBinary.Op;

public class DashHelper {

	public static String toLowerCase(String string) {
		return Character.toLowerCase(string.charAt(0)) + string.substring(1);
	}
	
	public static String toUpperCase(String string) {
		return Character.toUpperCase(string.charAt(0)) + string.substring(1);
	}
	
	public static Expr parameterize(String string) {
		return ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(string)));
	}
	
	/*
	 * If a Snapshot variable (assume a variable: var) originates from a Parameterized Concurrent State (assume with a parameter called p), then we create the following:
	 * var: p -> expr
	 */
	public static Expr createParameterizedVar(String var, Expr expr, DashModule module) {
		DashConcState concState = module.variable2ConcState.get(var);
		if (expr instanceof ExprUnary && concState.IEs.size() > 0) {
			ExprUnary exprUnary = (ExprUnary) expr;	
			int index = concState.IEs.size() - 1;
			if (exprUnary.op == ExprUnary.Op.LONEOF)
				expr = ExprBinary.Op.ANY_ARROW_LONE.make(null, null, ExprVar.make(null, concState.IEs.get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.ONEOF)
				expr = ExprBinary.Op.ANY_ARROW_ONE.make(null, null, ExprVar.make(null, concState.IEs.get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SOMEOF)
				expr = ExprBinary.Op.ANY_ARROW_SOME.make(null, null, ExprVar.make(null, concState.IEs.get(index)), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SETOF)
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.IEs.get(index)), exprUnary.sub);
			for (int i = concState.IEs.size() - 2; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.IEs.get(i)), expr);
			}
		} 
		else if (expr instanceof ExprVar) {
			for (int i = concState.IEs.size() - 1; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.IEs.get(i)), expr);
			}
		}
		else if (expr instanceof ExprBinary) {
			for (int i = concState.IEs.size() - 1; i >= 0; i--) {
				expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.IEs.get(i)), expr);
			}
		}
		return expr;
	}
	
	public static Expr createParameterizedExpr(String var, DashConcState concState) {
		Expr returnExpr = ExprVar.make(null, var);
		for (int i = concState.IEs.size() - 1; i >= 0; i--) {
			returnExpr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.IEs.get(i)), returnExpr);
		}

		return returnExpr;
	}
	
	public static Expr addParametersJoin (Expr expr, int totalIEs) {
        for (int i = 0; i < totalIEs; i++) {
        	expr = ExprBadJoin.make(null, null, ExprVar.make(null, "p" + i), expr);
        }
        return expr;
	}
	
	public static Expr addParametersArrow (Expr expr, DashConcState concState) {
		for (int i = concState.IEs.size() - 1; i >= 0; i--) {
			expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), expr);
		}
		return expr;
	}
	
	public static Expr addParametersArrow (Expr expr, int ies) {
		for (int i = ies - 1; i >= 0; i--) {
			expr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), expr);
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
        //expr = DashHelper.addParametersJoin(expr, parent.IEs.size());
        for (int i = 0; i < parent.IEs.size(); i++) { 
            a.add(ExprVar.make(null, "p" + i));
            decls.add(new Decl(null, null, null, null, a, ExprVar.make(null, parent.IEs.get(i))));
            a.clear();
        }
        return ExprQt.Op.ALL.make(null, null, decls, expr);
	}
	
	public static Expr constraintEquals(int conf, DashModule module, String type) {
		Expr equals = null;
		Expr s = createExprVar("s");
		Expr sNext = createExprVar("s_next");
		for (int key: module.confTuples) {
			if (key == conf) {
				continue;
			}
			Expr sConf = ExprBinary.Op.JOIN.make(null, null, s, createExprVar(type + key));
			Expr sNextConf = ExprBinary.Op.JOIN.make(null, null, sNext, createExprVar(type + key));
			Expr equal = ExprBinary.Op.EQUALS.make(null, null, sConf, sNextConf);
			equals = equals == null ? equal : ExprBinary.Op.AND.make(null, null, equals, equal);
		}
		return equals;
	}
	
	public static Expr constraintTaken (int conf, DashModule module) {
		Expr equals = null;
		Expr s = createExprVar("s");
		Expr sNext = createExprVar("s_next");
		for (int key: module.confTuples) {
			if (key == conf) {
				continue;
			}
			Expr sConf = ExprBinary.Op.JOIN.make(null, null, s, createExprVar("conf" + key));
			Expr sNextConf = ExprBinary.Op.JOIN.make(null, null, sNext, createExprVar("conf" + key));
			Expr equal = ExprBinary.Op.EQUALS.make(null, null, sConf, sNextConf);
			equals = equals == null ? equal : ExprBinary.Op.AND.make(null, null, equals, equal);
		}
		return equals;
	}
	
	public static Map<Integer, Expr> calculateConf2GotoExpr(DashTrans transition) {
		Map<Integer, Expr> conf2GotoExpr = new LinkedHashMap<Integer, Expr>();
		// For each Destination state
    	for (String key: transition.gotoExpr.gotoExprs.keySet()) {
    		// Create DestState expression
    		Expr destState = ExprVar.make(null, key);
    		// Get the parent concurrent state of the Destination state
    		DashConcState destStateParent = transition.gotoExpr.gotoExprs.get(key);
    		// Get the number of identifiers that maps to the state
    		int ieSize = destStateParent.IEs.size();
    		// Create the following (IE -> IE -> State)
            for (int i = ieSize - 1; i >= 0; i--) {
            	// p0 enters a state with concurrent states
            	if (i < transition.parentConcState.IEs.size()) {
            		destState = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), destState);
            	}
            	else {
            		destState = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, destStateParent.IEs.get(i)), destState);
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
    	for (String key: transition.fromExpr.fromExprs.keySet()) {
    		// Create SourceStste expression
    		Expr parentStateExited = ExprVar.make(null, transition.fromExpr.concStateBeingExited.modifiedName);
    		// Get the parent concurrent state of the Source state
    		DashConcState fromStateParent = transition.fromExpr.fromExprs.get(key);
    		int ieSize = fromStateParent.IEs.size();
    		// Create the following (IE -> IE -> State)
            for (int i = fromStateParent.IEs.size() - 1; i >= 0; i--) {
            	System.out.println("i: " + i + "IE: " +  fromStateParent.IEs.get(i) + "Size: " + fromStateParent.IEs.size() + " Trans Size: " + transition.parentConcState.IEs.size());
            	if (i < transition.parentConcState.IEs.size()) {
            		parentStateExited = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, "p" + i), parentStateExited);
            	}
            	else {
            		parentStateExited = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, fromStateParent.IEs.get(i)), parentStateExited);
            	}
            }
            
            if (!conf2FromExpr.containsKey(ieSize)) {
            	conf2FromExpr.put(ieSize, parentStateExited);
            } else {
            	// Create: (IE -> State) - (IE -> State)
            	Expr expr = ExprBinary.Op.MINUS.make(null, null, conf2FromExpr.get(ieSize), parentStateExited);
            	conf2FromExpr.put(ieSize, expr);
            }
    	}
		
		return conf2FromExpr;
	}
	
    /*************************** CREATING EXPRESSIONS ******************************/
	
	public static Expr createExprVar(String expr) {
		return ExprVar.make(null, expr);
	}
	
	public static Expr createExpBadJoin(String left, String right) {
		return ExprBadJoin.make(null, null, createExprVar(left), createExprVar(right)); 
	}
	
	public static Expr createExpBadJoin(String left, Expr right) {
		return ExprBadJoin.make(null, null, createExprVar(left), right); 
	}
	
	public static Expr createExpBadJoin(Expr left, String right) {
		return ExprBadJoin.make(null, null, left, createExprVar(right)); 
	}
	
	public static Expr createExpBadJoin(Expr left, Expr right) {
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
        	return (ExprBinary) ExprBinary.Op.OR.make(null, null, left, right);
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
    
    public static Expr conf(int i) {
    	return ExprVar.make(null, "conf" + i);
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
    	return createExpBadJoin(s(), conf(i));
    }
    
    public static Expr sNextConf(int i) {
    	return createExpBadJoin(sNext(), conf(i));
    }
    
    public static Expr sStable() {
    	return createExpBadJoin(s(), stable());
    }
    
    public static Expr _sStable() {
    	return createExpBadJoin(_s(), stable());
    }
    
    public static Expr sNextStable() {
    	return createExpBadJoin(sNext(), stable());
    }
    
    public static Expr sTaken(int i) {
    	return createExpBadJoin(s(), taken(i));
    }
    
    public static Expr sNextTaken(int i) {
    	return createExpBadJoin(sNext(), taken(i));
    }
    
    public static Expr sEvents(int i) {
    	return createExpBadJoin(s(), events(i));
    }
    
    public static Expr _sEvents(int i) {
    	return createExpBadJoin(_s(), events(i));
    }
    
    public static Expr sNextEvents(int i) {
    	return createExpBadJoin(sNext(), events(i));
    }
    
    public static Expr identifiers() {
    	return ExprVar.make(null, "Identifiers");
    }
    
    public static Expr trueExpr() {
    	return ExprVar.make(null, "True");
    }
    
    public static Expr falseExpr() {
    	return ExprVar.make(null, "False");
    }
	
    /*
     * Taken from the Dash.cup file. It is used for handling difficult parsing
     * ambiguities with Alloy expressions
     */
    private static Expr mult(Expr x) throws Err {
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
