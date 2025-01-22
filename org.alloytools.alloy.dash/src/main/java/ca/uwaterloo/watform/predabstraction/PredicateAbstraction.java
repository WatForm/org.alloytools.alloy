package ca.uwaterloo.watform.predabstraction;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.TransTable;
import ca.uwaterloo.watform.parser.VarTable;
import ca.uwaterloo.watform.alloyasthelper.CommandHelper;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;
import ca.uwaterloo.watform.dashtoalloy.Common;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.ast.DashVarDecls;
import ca.uwaterloo.watform.core.DashErrors;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.alloy4.ConstList;

import java.io.*;
import java.util.*;


public class PredicateAbstraction {

    // returns a deep copy of DashModule object
    // public static DashModule copyDashModule(DashModule d){

    //     assert(d.hasRoot()); // there is a Dash component in this module
    //     try {
    //         //System.out.println("In the try block of copyDashModule");
            
    //         DashModule dcopy = new DashModule(d);
    //         System.out.println("=========COPY==========");
    //         System.out.println(dcopy.transTableToString());
    //         System.out.println("===================");
    //         return dcopy;
            
    //     } catch(Exception e) {
    //         System.out.println("In catch block of copyDashModule");
    //         return d;
    //     }
    // } 

    // does not work; trying to change var and var' to s.var and sn.var without Common.translateExpr()
    public static Expr translatePrimedExpr(Expr e) {

        if (ExprHelper.isExprVar(e)) {
            String vname = ExprHelper.getVarName((ExprVar) e);
            if(DashStrings.hasPrime(vname)){
                return Common.nextJoinExpr(ExprHelper.createVar(DashStrings.removePrime(vname)));
            }
            else {
                return Common.curJoinExpr(e);
            }           
        }
        else if (ExprHelper.isExprUnary(e)) {
            return ExprHelper.createUnaryExpr(ExprHelper.getUnaryOp(e), translatePrimedExpr(ExprHelper.getSub(e)));
            
        } 
        else if (ExprHelper.isExprBinary(e)) {
            return ExprHelper.createBinaryExpr(translatePrimedExpr(ExprHelper.getLeft(e)),
                                               ExprHelper.getBinaryOp(e),
                                               translatePrimedExpr(ExprHelper.getRight(e)));
        } 
        else if (ExprHelper.isExprList(e)) {
            List<Expr> items = new ArrayList<Expr>();
            for (Expr sub : ExprHelper.getExprListItems(e)) {
                items.add(translatePrimedExpr(sub));
            }
            return ExprHelper.createExprList(ExprHelper.getListOp(e), items);
        } 
        else if (ExprHelper.isExprQt(e)) {
            return ExprHelper.createExprQt(ExprHelper.getQtOp(e), 
                                           ExprHelper.getQtDecls(e), 
                                           translatePrimedExpr(ExprHelper.getQtSub(e)));
        }

        else {
            return e;
        }

    }
    
    // This method takes a transition guard, action, and an abstraction predicate as input;
    // returns an Alloy predicate that is used to abstract the action 
    
    public static Command createQuery(List<Expr> args, DashModule d) {

        // create an Expr e: sn = s.DshSnapshot/next 
        List<Decl> snapshots = Common.curNextDecls();
        Expr svar = Common.curVar();
        Expr snvar = Common.nextVar();
        String nextSnapshot = DashStrings.snapshotName+DashStrings.SLASH+DashStrings.tracesNextName;
        Expr e = ExprHelper.createEquals(snvar, Common.curJoinExpr(ExprHelper.createVar(nextSnapshot)));
        
        Expr argsAndList = ExprHelper.createAndList(args);
        // translate guard && action && pred from var' notation to s.var and sn.var
        System.out.println("Formula being translated using my translate: "+argsAndList.toString());
        Expr translatedAndList = Common.translateExpr(argsAndList, d);
        //Expr translatedAndList = argsAndList;
        //Expr translatedAndList = translatePrimedExpr(argsAndList);
        //System.out.println("After translation: "+translatedAndList.toString());

        // add the snapshot expression e to the andList
        List<Expr> listItems = ExprHelper.getExprListItems(translatedAndList);
        listItems.add(e);

        Expr formula = ExprHelper.createAndList(listItems);            
        ExprQt q = ExprHelper.createSome(snapshots, formula);
        boolean check = false; //run command
        
        return CommandHelper.createCommand(check, 4, 4, q);
    }



    
    // This recursive method takes an Expr and breaks it down into a list of subexpressions (literals) based on the logical operators
    

    public static void decomposeExpr(Expr e, Set<Expr> literals) {

        if (ExprHelper.isExprConst(e) || ExprHelper.isExprVar(e)) {
            literals.add(e);
        }
        else if (ExprHelper.isExprUnary(e)) {
            decomposeExpr(ExprHelper.getSub(e), literals);
        } 
        else if (ExprHelper.isExprBinary(e)) {
            ExprBinary.Op op = ExprHelper.getBinaryOp(e);
            if(op.equals(ExprBinary.Op.AND) || op.equals(ExprBinary.Op.OR) || 
                op.equals(ExprBinary.Op.IMPLIES) || op.equals(ExprBinary.Op.IFF)){
                
                decomposeExpr(ExprHelper.getLeft(e), literals);
                decomposeExpr(ExprHelper.getRight(e), literals);
            }
            else {
                literals.add(e);
            }
        } 
        else if (ExprHelper.isExprList(e)) {
            for (Expr sub : ExprHelper.getExprListItems(e)) {
                decomposeExpr(sub, literals);
            }
        } 

        else {
            literals.add(e);
        }

        // else if (expr instanceof ExprCall) {
        //     for (Expr sub : ((ExprCall) expr).args) {
        //         decomposeExpr(sub, literals);
        //     }
        // } 
        // else if (expr instanceof ExprQt) {
        //     decomposeExpr(((ExprQt) expr).sub, literals);
        
        // later: move_exists, move_forall, exists_over_or, forall_over_and
        //        Breaking down preds based on scopes 
            
        // } 
        // else if (expr instanceof ExprLet) {
        //     decomposeExpr(((ExprLet) expr).expr, literals);
        // }
        
    }

     
    //    This method takes a concrete guard exp and a map of abs preds -> BVs and
    //    returns an Expr where the guard is abstracted.
    
    public static Expr replaceSubexp(Expr e, HashMap<Expr, Expr> map) {

        if(map.containsKey(e)){
            return map.get(e);
        }
        else if(ExprHelper.isExprUnary(e)){
            Expr sub = replaceSubexp(ExprHelper.getSub(e), map);
            return ExprHelper.createUnaryExpr(ExprHelper.getUnaryOp(e), sub);
        }
        else if(ExprHelper.isExprBinary(e)){
            ExprBinary.Op op = ExprHelper.getBinaryOp(e);
            if(op.equals(ExprBinary.Op.AND) || op.equals(ExprBinary.Op.OR) || 
                op.equals(ExprBinary.Op.IMPLIES) || op.equals(ExprBinary.Op.IFF)) {

                Expr left = replaceSubexp(ExprHelper.getLeft(e), map);
                Expr right = replaceSubexp(ExprHelper.getRight(e), map);
                return ExprHelper.createBinaryExpr(left, op, right);
            }
            // should be unreachable
            else {
                return map.get(e);
            }

        }
        else if(ExprHelper.isExprList(e)){
            ExprList.Op op = ExprHelper.getListOp(e);
            List<Expr> args = new ArrayList<Expr>();
            for (Expr sub : ExprHelper.getExprListItems(e)) {
                args.add(replaceSubexp(sub, map));
            }
            return ExprHelper.createExprList(op, args);
        }
        else {
            System.out.println("The Alloy expression " + e.toString() + " cannot be abstracted with the set of predicates");
            return e;
        }
    }

    // TODO
    // public static Expr createAbstractExpr(List<Expr> items, HashMap<Expr, Expr> predVarMap, CompModule c, A4Reporter rep) {

    //     if(items == null){
    //         return null;
    //     }

    //     List<Expr> absExprList = new ArrayList<Expr>();

    //     for(Expr i: items) {
    //         for(Expr p: predVarMap.keySet()) {
    //             List<Expr> queryArgs = new ArrayList<Expr>();
    //             Expr negp = ExprHelper.createNot(p);
    //             Expr v = predVarMap.get(p);

    //             queryArgs.add(i);
    //             queryArgs.add(negp);
    //             Command query = createQuery(queryArgs, d);
    //             A4Options options = new A4Options();
                    
    //             A4Solution solution = MainFunctions.executeCommand(query, c, rep, options);
    //             if(solution.satisfiable()){
                    
    //                 queryArgs.remove(negp);
    //                 queryArgs.add(p);
    //                 Command query = createQuery(queryArgs, d);
    //                 A4Solution sol2 = MainFunctions.executeCommand(query, c, rep, options);

    //                 if(!sol2.satisfiable()){
    //                     absExprList.add(ExprHelper.createIsFalse(Common.nextJoinExpr(v)));
    //                 }
    //             }
    //             else {
    //                 absExprList.add(ExprHelper.createIsTrue(Common.nextJoinExpr(v)));
    //             } 
                    
    //         }

    //         Expr absExpr = ExprHelper.createAndFromList(absExprList);
    //         // transAbsAction.put(t, absAction);

    //     }

    // }


     
    // This method takes a DashModule object as input and returns the abstract model

    public static DashModule createAbstractModel(String inputFilename) {

        A4Reporter rep = new A4Reporter();

        DashModule d = MainFunctions.parseDashFile(inputFilename, rep);
        System.out.println("Parsed Dash file");
        if (d == null) 
            DashErrors.emptyFile(inputFilename);
                
        d = MainFunctions.resolveDash(d, rep);
        System.out.println("Resolved Dash"); 

        CompModule c = MainFunctions.translate(d, rep);
        System.out.println("Translated Dash to Alloy"); 
        c = MainFunctions.resolveAlloy(c,rep);
        System.out.println("Resolved Alloy");
                

        //get all the transition names, guards, and actions store in a list
        List<String> allTransNames = d.getAllTransNames();
        HashMap<String, Expr> allTransGuards = new HashMap<String, Expr>();
        HashMap<String, Expr> allTransActions = new HashMap<String, Expr>();

        for(String t: allTransNames){
            Expr g = d.getTransWhen(t);
            Expr a = d.getTransDo(t);
            if(g != null) {
                
                allTransGuards.put(t, g);
                // try {
                //     allTransGuards.put(t, Common.translateExpr(g, d));
                // }
                // catch(Exception e){
                //     System.out.println("Exception while copying the guard of the transition "+t+" : "+g.toString());
                //     e.printStackTrace(System.out);
                // }
            }
            if(a != null) {
                
                allTransActions.put(t, a);
                // try {
                //     allTransActions.put(t, Common.translateExpr(a, d));
                // }
                // catch(Exception e) {
                //     System.out.println("Exception while copying the action of the transition "+t+" : "+a.toString());
                //     e.printStackTrace(System.out);
                // }
            }
        }

        //for now, if a model has no guards, we do not abstract the model.
        if(allTransGuards.isEmpty()){
            System.out.println("The given Dash+ model does not have any guards on the transitions");
            return d;
        }



        //create a list/set of abstraction predicates from the guards, decomposed by logical operators

        List<Expr> absPreds = new ArrayList<Expr>();

        for(Map.Entry<String, Expr> entry: allTransGuards.entrySet()) {
            Set<Expr> gsubs = new HashSet<Expr>();
            Expr g = entry.getValue(); 
            decomposeExpr(g, gsubs);
            for(Expr gs: gsubs){
                absPreds.add(gs);
            }
        }


        // List of boolean variables corresponding to the abstraction predicates
        List<String> bvNames = new ArrayList<String>();
        for(int i = 0; i < absPreds.size(); i++) {
            bvNames.add("B"+Integer.toString(i));
        }
        
        // get rid of createOne; oneOf?
        Expr boolType = ExprHelper.createOne(ExprHelper.createVar(DashStrings.boolName));
        
        HashMap<Expr, Expr> predVarMap = new HashMap<Expr, Expr>();
        int i = 0;
        for(Expr p: absPreds) {
            Expr v = ExprHelper.createVar(bvNames.get(i));
            i += 1;
            predVarMap.put(p, v);
        }

        //Inits and facts also need to be translated 
        List<Expr> inits = d.getInits();
        List<Expr> invs = d.getInvs();

        // if(inits != null) {
        //     if(inits.size() > 0){
        //         for(Expr i: inits) {
        //             for(Expr p: absPreds) {
        //                 List<Expr> queryArgs = new ArrayList<Expr>(inits);
        //                 Expr negp = ExprHelper.createNot(p);
        //                 queryArgs.add(negp);
        //                 Command query = createQuery(queryArgs, d);
        //                 A4Options options = new A4Options();
        //                 A4Solution solution = MainFunctions.executeCommand(query, c, rep, options);
        //             }
        //         }
        //     }
        // }
        
        // create a copy of the resolved Dash module
        // DashModule absModel = copyDashModule(d);

        // now translate it to Alloy and resolve
        // CompModule c = MainFunctions.translate(d, rep);
        // c = MainFunctions.resolveAlloy(c,rep);

        HashMap<String, Expr> transAbsGuard = new HashMap<String, Expr>();
        HashMap<String, Expr> transAbsAction = new HashMap<String, Expr>();

        System.out.println("Just before the for loop: debugging elevator.dsh");

        for(String t: allTransNames) {
            
            Expr guard = allTransGuards.get(t);
            Expr action = allTransActions.get(t);
            
            if(guard != null && action != null){

                List<Expr> absActionVars = new ArrayList<Expr>(); // abstract action

                for(Expr p: absPreds) {
                    Expr negp = ExprHelper.createNot(p);
                    Expr v = predVarMap.get(p);
                    List<Expr> queryArgs = new ArrayList<Expr>();
                    queryArgs.add(guard);
                    queryArgs.add(action);
                    queryArgs.add(negp);

                    // Parse, resolve, and translate the dash model again 
                    d = MainFunctions.parseDashFile(inputFilename, rep);
                    d = MainFunctions.resolveDash(d, rep);
                    c = MainFunctions.translate(d, rep);
                    c = MainFunctions.resolveAlloy(c, rep);

                    Command query = createQuery(queryArgs, d);
                    System.out.println("Query created");
                    A4Options options = new A4Options();
                    
                    A4Solution solution = MainFunctions.executeCommand(query, c, rep, options);
                    if(solution.satisfiable()){
                        System.out.println("Ran query for "+t+" and neg predicate "+p.toString()+" : SAT");
                        queryArgs.remove(negp);
                        queryArgs.add(p);
                        Command query2 = createQuery(queryArgs, d);
                        A4Solution sol2 = MainFunctions.executeCommand(query2, c, rep, options);

                        if(!sol2.satisfiable()){
                            System.out.println("Ran query for "+t+" and predicate "+p.toString()+" : UNSAT");
                            absActionVars.add(ExprHelper.createIsFalse(Common.nextJoinExpr(v)));
                        }
                    }
                    else {
                        System.out.println("Ran query for "+t+" and neg predicate "+p.toString()+" : UNSAT");
                        absActionVars.add(ExprHelper.createIsTrue(Common.nextJoinExpr(v)));
                    } 
                    
                }

                Expr absAction = ExprHelper.createAndFromList(absActionVars);
                transAbsAction.put(t, absAction);

                Expr absGuard = replaceSubexp(guard, predVarMap);
                transAbsGuard.put(t, absGuard);

            }
        }

        for(String t: allTransNames){
            Expr g = transAbsGuard.get(t);
            Expr a = transAbsAction.get(t);
            if(g != null){
                // System.out.println("Testing: Abstract guard...");
                // System.out.println(g.toString());
                d.setTransWhen(t, transAbsGuard.get(t));
            }
            if(a != null){
                d.setTransDo(t, transAbsAction.get(t));
            }
            
        }
        // TODO: add boolean variables to a new varTable

        //vartable varelemt can take empty list for prms
        //invs and inits just run query as inv & pred

        // System.out.println("=========ORIGINAL==========");
        // System.out.println(d.transTableToString());
        // System.out.println("===================");

        // System.out.println("=========ABSTRACT==========");
        // System.out.println(absModel.transTableToString());
        // System.out.println("===================");


        return d;
        
    }

}
