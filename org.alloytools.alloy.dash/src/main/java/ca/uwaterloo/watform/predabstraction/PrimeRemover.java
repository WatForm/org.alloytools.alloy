package ca.uwaterloo.watform.predabstraction;

import java.util.stream.Collectors;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import static ca.uwaterloo.watform.core.DashStrings.*;

import ca.uwaterloo.watform.alloyasthelper.CommandHelper;
import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.ast.DashVarDecls;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.dashtoalloy.Common;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;
import ca.uwaterloo.watform.parser.CompModuleHelper;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.TransTable;
import ca.uwaterloo.watform.parser.VarTable;
import ca.uwaterloo.watform.predabstraction.AbstractionQuery;
import ca.uwaterloo.watform.predabstraction.PredicateAbstraction;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

public class PrimeRemover {
    private static Expr convert(Expr e) {
        if(e == null) return null;
        System.out.println(e + ": " + e.getClass().getName());
        if(DashRef.isDashRef(e) && hasPrime(((DashRef)e).getName())) {
            System.out.println("Primed DashRef");
            return DashRef.createVarDashRef(removePrime(((DashRef)e).getName()),
                                            ((DashRef)e).getParamValues());
            // System.out.println(((DashRef) e).getName());
            // List<Expr> converted = new ArrayList<Expr>();
            // for(Expr orgExpr : ((DashRef) e).getParamValues()) {
            // 	System.out.println("orgExpr: " + orgExpr);
            // 	System.out.println("converted: " + convert(orgExpr));
            // 	converted.add(convert(orgExpr));
            // }
        } else if(isPrimedVar(e)) {
			// not tested
            System.out.println("Primed Var");
            return getSub(e);
        } else if(isExprUnary(e)) {
            System.out.println("Unary Expr");
            return createUnaryExpr(getUnaryOp(e), convert(getSub(e)));
        } else if(isExprBinary(e)) {
            System.out.println("Binary Expr");
            return createBinaryExpr(convert(getLeft(e)), getBinaryOp(e),
                                    convert(getRight(e)));
        } else if(isExprBadJoin(e)) {
            System.out.println("Bad Join");
            return ExprBadJoin.make(
                e.pos,
                e.closingBracket,
                convert(getLeft(e)),
                convert(getRight(e)));

        } else if(e instanceof ExprCall) {
            // not tested
            System.out.println("ExprCall");
            return ExprCall.make(e.pos, e.closingBracket,
                                 ((ExprCall)e).fun,
                                 ((ExprCall)e)
                                     .args.stream()
                                     .map(i -> convert(i))
                                     .collect(Collectors.toList()),
                                 ((ExprCall)e).extraWeight);
        } else if(e instanceof ExprChoice) {
            // not tested
            System.out.println("ExprChoice");
            ConstList<Expr> converted = (ConstList<Expr>)((ExprChoice)e)
                                    .choices.stream()
                                    .map(i -> convert(i))
                                    .collect(Collectors.toList());
            return ExprChoice.make(false, e.pos, converted,
                                   ((ExprChoice)e).reasons);

        } else if(e instanceof ExprITE) {
			// not tested
            System.out.println("ExprITE");
            return ExprITE.make(
                e.pos,
                convert(getCond(e)),
                convert(getLeft(e)),
                convert(getRight(e)));
		} else if(isExprList(e)) {
			// not tested
            System.out.println("List");
            List<Expr> converted = new ArrayList<Expr>();
            for(Expr orgExpr : getExprListItems(e)) {
                converted.add(convert(orgExpr));
            }
            return createExprList(getListOp(e), converted);
        } else {
			// null
            // isExprVar
			// instanceof ExprLet
			// instanceof ExprQT
			// instance of ExprConstant
            return e;
        }
    }
    public static DashModule removePrimedInAction(DashModule d) {
        System.out.println("Removing Primes");
        List<String> transNames = d.getAllTransNames();

        for(String transName : transNames) {
            System.out.println(transName);
            Expr action = d.getTransDo(transName);
            System.out.println("Before: " + action);
            action = convert(action);
            d.setTransDo(transName, action);
            action = d.getTransDo(transName);
            System.out.println("After: " + action);
            System.out.println();
        }

        return d;
    }
}
