package ca.uwaterloo.watform.predabstraction;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;
import ca.uwaterloo.watform.parser.TransTable;
import ca.uwaterloo.watform.parser.VarTable;
import ca.uwaterloo.watform.alloyasthelper.CommandHelper;
import ca.uwaterloo.watform.alloyasthelper.ExprHelper;
import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashFQN;
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

    public static String negString = "neg";
    public static String boolVarString = "B";
    public static String guardString = "guard";
    public static String actionString = "action";
    public static String initsString = "inits";
    public static String invString = "inv";

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


    
    // This method takes a transition guard, action, and an abstraction predicate as input;
    // returns an Alloy predicate that is used to abstract the action 
    
    // public static Command createQuery(List<Expr> args, DashModule d, CompModule comp, String label) {

    //     // create an Expr e: sn = s.DshSnapshot/next 
    //     List<Decl> snapshots = Common.curNextDecls();
    //     Expr svar = Common.curVar();
    //     Expr snvar = Common.nextVar();
    //     String nextSnapshot = DashStrings.snapshotName+DashStrings.SLASH+DashStrings.tracesNextName;
    //     Expr e = ExprHelper.createEquals(snvar, Common.curJoinExpr(ExprHelper.createVar(nextSnapshot)));
        
    //     Expr argsAndList = ExprHelper.createAndList(args);
    //     // translate guard && action && pred from var' notation to s.var and sn.var
    //     // System.out.println("Formula being translated using my translate: "+argsAndList.toString());
    //     Expr translatedAndList = Common.translateExpr(argsAndList, d);
    //     //Expr translatedAndList = argsAndList;
    //     //Expr translatedAndList = translatePrimedExpr(argsAndList);
    //     System.out.println("Query formula after translation: "+translatedAndList.toString());

    //     // add the snapshot expression e to the andList
    //     List<Expr> listItems = ExprHelper.getExprListItems(translatedAndList);
    //     listItems.add(e);

    //     Expr formula = ExprHelper.createAndList(listItems);            
    //     Expr q = ExprHelper.createSome(snapshots, formula);
    //     boolean check = false; //run command
        
    //     return CommandHelper.createCommand(comp, check, 4, 4, q, label);
    // }

    /*
        Creates a predicate:

        pred query_tfqn_bv_neg[s, sn: DshSnapshot] {
            sn = s.DshSnapshot/next
            tfqn_guard
            tfqn_action
            abs_pred
        }
    */
    public static void addQueryPred(List<Expr> args, DashModule d, CompModule c, String name) {

        List<Expr> body = new ArrayList<Expr>();

        // create an Expr e: sn = s.DshSnapshot/next 
        List<Decl> snapshots = Common.curNextDecls();
        Expr svar = Common.curVar();
        Expr snvar = Common.nextVar();
        String nextSnapshot = DashStrings.snapshotName+DashStrings.SLASH+DashStrings.tracesNextName;
        Expr sn_s = ExprHelper.createEquals(snvar, Common.curJoinExpr(ExprHelper.createVar(nextSnapshot)));
        
        body.add(sn_s);
        for(Expr e: args) {
            body.add(Common.translateExpr(e, d));
        }

        String predString = d.addPredSimple(name, Common.curNextDecls(), body);
        System.out.println("\n******************");
        System.out.println(predString);
        System.out.println("\n******************");
        d.alloyString += predString;

        boolean check = false;
        CommandHelper.createCommand(c, check, 4, 4, name);
        System.out.println("Query "+name+" created.");
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
    
    public static Expr replaceSubexp(Expr e, HashMap<Expr, ExprVar> map) {

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
    public static void addAbstractionQueries(List<Expr> items, HashMap<Expr, ExprVar> predVarMap, DashModule d, CompModule c, String name) {

        if(items != null){
            for(Expr p: predVarMap.keySet()) {
                List<Expr> queryArgs = new ArrayList<Expr>(items);
                Expr negp = ExprHelper.createNot(p);
                ExprVar v = predVarMap.get(p);
                String qname = name + "_" + ExprHelper.getVarName(v) + "_" + negString;

                queryArgs.add(negp);
                addQueryPred(queryArgs, d, c, qname);

                qname = name + "_" + ExprHelper.getVarName(v);            
                queryArgs.remove(negp);
                queryArgs.add(p);
                addQueryPred(queryArgs, d, c, qname);                     
            }
        }
    }


     
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

        int cmdCtr = c.getAllCommands().size();
                

        //get all the transition names, guards, and actions store in a list
        List<String> allTransNames = d.getAllTransNames();
        HashMap<String, Expr> allTransGuards = new HashMap<String, Expr>();
        HashMap<String, Expr> allTransActions = new HashMap<String, Expr>();

        for(String t: allTransNames){
            Expr g = d.getTransWhen(t);
            Expr a = d.getTransDo(t);
            if(g != null) { 
                allTransGuards.put(t, g);
            }
            if(a != null) {
                allTransActions.put(t, a);
            }
        }

        List<Expr> inits = d.getInits();
        List<Expr> invs = d.getInvs();

        //for now, if a model has no guards, we do not abstract the model.
        if(allTransGuards.isEmpty() && invs.size() == 0){
            System.out.println("The given Dash+ model does not have any guards or invariants (sources of predicates)");
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

        for(Expr inv: invs) {
            Set<Expr> isubs = new HashSet<Expr>(); 
            decomposeExpr(inv, isubs);
            for(Expr is: isubs){
                absPreds.add(is);
            }
        }

        // get rid of createOne; oneOf?
        //Expr boolType = ExprHelper.createVar(DashStrings.boolName);
        

        HashMap<Expr, ExprVar> predVarMap = new HashMap<Expr, ExprVar>();
        int i = 0;
        for(Expr p: absPreds) {
            predVarMap.put(p, ExprHelper.createVar(boolVarString + Integer.toString(i)));
            i += 1;
        }

        //Inits and facts also need to be translated 
        
        if(inits.size() > 0){
            addAbstractionQueries(inits, predVarMap, d, c, initsString);
        }

        if(invs.size() > 0) {
            i = 0;
            for(Expr inv: invs){
                List<Expr> arg = new ArrayList<Expr>();
                arg.add(inv);
                addAbstractionQueries(arg, predVarMap, d, c, invString + Integer.toString(i));
                i += 1;
            }
        }

        for(Map.Entry<String, Expr> entry: allTransGuards.entrySet()) {
            Expr g = entry.getValue(); 
            List<Expr> arg = new ArrayList<Expr>();
            arg.add(g);
            String qname = guardString + "_" + DashFQN.translateFQN(entry.getKey());
            addAbstractionQueries(arg, predVarMap, d, c, qname);
        }

        for(String t: allTransNames) {
            Expr guard = allTransGuards.get(t);
            Expr action = allTransActions.get(t);
            List<Expr> arg = new ArrayList<Expr>();
            arg.add(guard);
            arg.add(action);
            String qname = actionString + "_" + DashFQN.translateFQN(t);
            addAbstractionQueries(arg, predVarMap, d, c, qname);
        }

        /*HashMap<String, Expr> transAbsGuard = new HashMap<String, Expr>();
        HashMap<String, Expr> transAbsAction = new HashMap<String, Expr>();

        for(String t: allTransNames) {
            
            Expr guard = allTransGuards.get(t);
            Expr action = allTransActions.get(t);
            
            if(guard != null && action != null){

                //List<Expr> absActionVars = new ArrayList<Expr>(); // abstract action

                for(Expr p: absPreds) {
                    Expr negp = ExprHelper.createNot(p);
                    ExprVar v = predVarMap.get(p);
                    String tname = DashFQN.translateFQN(t);
                    //translatefqn from dashfqn
                    String qname = tname + "_" + actionString + negString +ExprHelper.getVarName(v);
                    System.out.println("Query name: " + qname);
                    List<Expr> queryArgs = new ArrayList<Expr>();
                    queryArgs.add(guard);
                    queryArgs.add(action);
                    queryArgs.add(negp);

                    addQueryPred(queryArgs, d, c, qname);

                    // System.out.println("Query created");
                    
                    // c = MainFunctions.resolveAlloy(c, rep);
                    // Command query = c.commands.get(c.commands.size() - 1);

                    // A4Options options = new A4Options();
                    // A4Solution solution = MainFunctions.executeCommand(query, c, rep, options);

                    // if(solution.satisfiable()){
                    //     System.out.println("Ran query for "+t+" and neg predicate "+p.toString()+" : SAT");
                    //     queryArgs.remove(negp);
                    //     queryArgs.add(p);
                    //     qname = tname + "_" + ExprHelper.getVarName(v);
                    //     CompModule c2 = MainFunctions.translate(d, rep);
                    //     //Command query2 = createQuery(queryArgs, d, c2, t+"_"+ExprHelper.getVarName(v));
                        
                    //     addQueryPred(queryArgs, d, c2, qname);
                    //     query = c2.commands.get(c2.commands.size() - 1);

                    //     c2 = MainFunctions.resolveAlloy(c2, rep);
                    //     A4Solution sol2 = MainFunctions.executeCommand(query, c2, rep, options);

                    //     if(!sol2.satisfiable()){
                    //         System.out.println("Ran query for "+t+" and predicate "+p.toString()+" : UNSAT");
                    //         absActionVars.add(ExprHelper.createIsFalse(Common.nextJoinExpr(v)));
                    //     }
                    // }
                    // else {
                    //     System.out.println("Ran query for "+t+" and neg predicate "+p.toString()+" : UNSAT");
                    //     absActionVars.add(ExprHelper.createIsTrue(Common.nextJoinExpr(v)));
                    // } 

                    queryArgs.remove(negp);
                    queryArgs.add(p);
                    qname = tname + "_" + actionString + "_" + ExprHelper.getVarName(v);
                    addQueryPred(queryArgs, d, c, qname);
                }

                // Expr absAction = ExprHelper.createAndFromList(absActionVars);
                // transAbsAction.put(t, absAction);

                // Expr absGuard = replaceSubexp(guard, predVarMap);
                // transAbsGuard.put(t, absGuard);

            }
        }*/

        c = MainFunctions.resolveAlloy(c, rep);
        List<Command> cmds = new ArrayList<Command>();

        for(Command cmd: c.getAllCommands()) {
            cmds.add(cmd);
        }

        HashMap<String, Boolean> queryResultMap = new HashMap<String, Boolean>();

        for(i = cmdCtr; i < cmds.size(); i++) {
            Command query = cmds.get(i);
            String name = query.label;
            A4Options options = new A4Options();
            A4Solution solution = MainFunctions.executeCommand(query, c, rep, options);
            System.out.println("Executed query: "+name);
            queryResultMap.put(name, solution.satisfiable());
        }

        for(Map.Entry<String, Boolean> entry: queryResultMap.entrySet()) {

            String qname = entry.getKey();
            Boolean result = entry.getValue();

            //inits
            if(qname.startsWith(initsString)) {

            }

            //invs

            if(qname.startsWith(invString)) {
                
            }

            //guards
            if(qname.startsWith(guardString)) {
                
            }

            //actions
            if(qname.startsWith(actionString)) {
                
            }
        }





        // for(String t: allTransNames){
        //     Expr g = transAbsGuard.get(t);
        //     Expr a = transAbsAction.get(t);
        //     if(g != null){
        //         // System.out.println("Testing: Abstract guard...");
        //         // System.out.println(g.toString());
        //         d.setTransWhen(t, transAbsGuard.get(t));
        //     }
        //     if(a != null){
        //         d.setTransDo(t, transAbsAction.get(t));
        //     }
            
        // }
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
