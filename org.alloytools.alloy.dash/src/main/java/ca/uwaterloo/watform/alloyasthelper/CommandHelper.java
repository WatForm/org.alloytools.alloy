package ca.uwaterloo.watform.alloyasthelper;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.SafeList;

import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

import java.util.*;

public class CommandHelper {

	public static String toString(Command c) {
		return c.toString();
	}

	public static Command changeFormula(Command c, Expr e) {
		return c.change(e);
	}

	public static Command changeAllScopes(Command c, ConstList<CommandScope> scope) {
		return c.change(scope);
	}

	public static Command changeScopeForSig(Command c, Sig sig, boolean isExact, int newScope) {
		return c.change(sig, isExact, newScope);
	}

	public static Command createCommand(CompModule comp, boolean check, int overallScope, int bitwidth, String predName) {

		ExprVar commandKeyword = (check)? ExprHelper.createVar("c") : ExprHelper.createVar("r");
		ExprVar pred = null;

		List<Func> funcs = comp.getAllFunc().makeCopy();
		for(Func f: funcs) {
			if(f.isPred && f.label == predName) {
				pred = (ExprVar) f.labelExpr();
			}
		}

		if(pred == null) {
			pred = ExprHelper.createVar(predName, Type.FORMULA);
		}

		comp.addCommand(false, null, pred, commandKeyword, overallScope, bitwidth, -1, -1, -1, -1, null, pred);

		ConstList<Command> c = comp.getAllCommands();
		Command cmd = c.get(c.size()-1);

		return cmd;
	}
}