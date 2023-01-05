package ca.uwaterloo.watform.transform;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ca.uwaterloo.watform.ast.DashSuperState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.ast.Expr;

public class TranslationFromCoreDash {
	boolean isCreatingEnabledAfterPred;
	boolean isCreatingPreCond;
	boolean isCreatingInit;
	boolean isCreatingInvariant;
	boolean isCreatingExprQt;
	boolean isCreatingSnapshot;
	 
	Map <Integer, List<DashTrans>> eventSize2Trans;
	Map<String, DashSuperState> changedLocalVars; // Variables changed only locally
	List<String> changedRefVars; // Variables changed by reference in the transitions being checked
	Map<String, DashSuperState> changedVars; // Keep a track of when a variable has been changed during a transition
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
	boolean legalConstraint;
	
	public TranslationFromCoreDash() {
		eventSize2Trans = new LinkedHashMap<>();
		changedLocalVars = new LinkedHashMap<>();
		changedRefVars = new ArrayList<>();
		changedVars = new LinkedHashMap<>();
		paramBuffer = new LinkedHashMap<>();
		paramBufferChanged = new LinkedHashMap<>();
		localBufferChanged = new LinkedHashMap<>();
		bufferCommands = Arrays.asList(new String[]{"addFirst", "add", "remove", "removeFirst"});
		bufferFuncCommands = Arrays.asList(new String[]{"firstElem"});
		universalQuantBuffers = new LinkedHashMap<>();
	}
}
