package ca.uwaterloo.watform.alloyasthelper;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.alloy4.ConstList;

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

	public static Command createCommand(boolean check, int overallScope, int bitwidth, Expr formula) {
		ExprVar commandKeyword = ExprHelper.createVar("c");
		Command c = new Command(null, null, "", check, overallScope, bitwidth, -1, -1, -1, -1, null, null, commandKeyword, formula, null);
		System.out.println(c.toString());
		return c;
         
	}


	// Refer MainFunctions.ExecuteCommand();

	/* public static A4Solution runCommand(Command c, CompModule world) {

		try {
			A4Options options = new A4Options();
            options.solver = A4Options.SatSolver.SAT4J;

            A4Solution solution = TranslateAlloyToKodkod.execute_command(null, world.getAllReachableSigs(), c, options);
            return solution;

		}
		catch(Exception e) {
			e.printStackTrace();
		}
	}*/ 

}

// /**
//      * Constructs a new Command object.
//      *
//      * @param check - true if this is a "check"; false if this is a "run"
//      * @param overall - the overall scope (0 or higher) (-1 if no overall scope was
//      *            specified)
//      * @param bitwidth - the integer bitwidth (0 or higher) (-1 if it was not
//      *            specified)
//      * @param maxseq - the maximum sequence length (0 or higher) (-1 if it was not
//      *            specified)
//      * @param mintime - the minimal trace length (0 or higher) (-1 if it was not
//      *            specified)
//      * @param maxtime - the maximal trace length (0 or higher) (-1 if it was not
//      *            specified)
//      * @param formula - the formula that must be satisfied by this command
//      */
//     //extended with time scopes
//     public Command(boolean check, int overall, int bitwidth, int maxseq, int mintime, int maxtime, ExprVar commandKeyword, Expr formula) throws ErrorSyntax {
//         this(null, null, "", check, overall, bitwidth, maxseq, mintime, maxtime, -1, null, null, commandKeyword, formula, null);
//     }

//     /**
//      * Constructs a new Command object.
//      *
//      * @param check - true if this is a "check"; false if this is a "run"
//      * @param overall - the overall scope (0 or higher) (-1 if no overall scope was
//      *            specified)
//      * @param bitwidth - the integer bitwidth (0 or higher) (-1 if it was not
//      *            specified)
//      * @param maxseq - the maximum sequence length (0 or higher) (-1 if it was not
//      *            specified)
//      * @param formula - the formula that must be satisfied by this command
//      */
//     public Command(boolean check, int overall, int bitwidth, int maxseq, ExprVar commandKeyword, Expr formula) throws ErrorSyntax {
//         this(null, null, "", check, overall, bitwidth, maxseq, -1, -1, -1, null, null, commandKeyword, formula, null);
//     }

//     /**
//      * Constructs a new Command object.
//      *
//      * @param pos - the original position in the file (must not be null)
//      * @param label - the label for this command (it is only for pretty-printing and
//      *            does not have to be unique)
//      * @param check - true if this is a "check"; false if this is a "run"
//      * @param overall - the overall scope (0 or higher) (-1 if no overall scope was
//      *            specified)
//      * @param bitwidth - the integer bitwidth (0 or higher) (-1 if it was not
//      *            specified)
//      * @param maxseq - the maximum sequence length (0 or higher) (-1 if it was not
//      *            specified)
//      * @param minprefix - the minimal trace prefix length (0 or higher) (-1 if it
//      *            was not specified)
//      * @param maxprefix - the maximal trace prefix length (0 or higher) (-1 if it
//      *            was not specified)
//      * @param expects - the expected value (0 or 1) (-1 if no expectation was
//      *            specified)
//      * @param scope - a list of scopes (can be null if we want to use default)
//      * @param additionalExactSig - a list of sigs whose scope shall be considered
//      *            exact though we may or may not know what the scope is yet
//      * @param formula - the formula that must be satisfied by this command
//      */
//     public Command(Pos pos, Expr e, String label, boolean check, int overall, int bitwidth, int maxseq, int minprefix, int maxprefix, int expects, Iterable<CommandScope> scope, Iterable<Sig> additionalExactSig, ExprVar commandKeyword, Expr formula, Command parent) {
//         if (pos == null)
//             pos = Pos.UNKNOWN;
//         this.nameExpr = e;
//         this.commandKeyword = commandKeyword;
//         this.formula = formula;
//         this.pos = pos;
//         this.label = (label == null ? "" : label);
//         this.check = check;
//         this.overall = (overall < 0 ? -1 : overall);
//         this.bitwidth = (bitwidth < 0 ? -1 : bitwidth);
//         this.maxseq = (maxseq < 0 ? -1 : maxseq);
//         this.maxprefix = (maxprefix < 1 ? -1 : maxprefix);
//         this.minprefix = (minprefix < 1 ? -1 : minprefix);
//         this.maxstring = (-1);
//         this.expects = (expects < 0 ? -1 : (expects > 0 ? 1 : 0));
//         this.scope = ConstList.make(scope);
//         this.additionalExactScopes = ConstList.make(additionalExactSig);
//         this.parent = parent;
//     }