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
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.ast.DashVarDecls;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.predabstraction.AbstractionQuery;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Pos;
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
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;


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

    /*
        Creates a predicate:

        pred query_tfqn_bv_neg[s, sn: DshSnapshot] {
            sn = s.DshSnapshot/next
            tfqn_guard
            tfqn_action
            abs_pred
        }
    */
    public static AbstractionQuery addQueryPred(List<Expr> args, 
                                                DashModule d, 
                                                CompModule c, 
                                                String name,     
                                                AbstractionQuery.QueryType typ,
                                                Expr pred,
                                                Boolean neg) {

        List<Expr> body = new ArrayList<Expr>();
        Expr svar = Common.curVar();

        AbstractionQuery q = new AbstractionQuery(name, name, typ, pred, neg);

        if(typ == AbstractionQuery.QueryType.ACTION) {
            List<Decl> snapshots = Common.curNextDecls();
            body.add(ExprHelper.createPredCall(DashStrings.smallStepName, Common.curNextVars()));

            for(Expr e: args) {
                body.add(Common.translateExpr(e, d));
            }

            String predBody = d.addPredSimple(name, Common.curNextDecls(), body);
            q.setPredBody(predBody);
            System.out.println("\n******************");
            System.out.println(predBody);
            System.out.println("\n******************");
        }
        else {
            if(typ == AbstractionQuery.QueryType.INIT) {
                List<Expr> curvar = new ArrayList<Expr>();
                curvar.add(Common.curVar());
                body.add(ExprHelper.createPredCall(DashStrings.initFactName, curvar));
            }
            for(Expr e: args) {
                body.add(Common.translateExpr(e, d));
            }
            List<Decl> snapshot = new ArrayList<Decl>();
            snapshot.add(Common.curDecl());
            String predBody = d.addPredSimple(name, snapshot, body);
            q.setPredBody(predBody);
            System.out.println("\n******************");
            System.out.println(predBody);
            System.out.println("\n******************");
        }

        boolean check = false;
        Command cmd = CommandHelper.createCommand(c, check, 4, 4, name);
        q.setCommand(cmd);
        q.setCmdBody(cmd.toString() + "\n");
        System.out.println("Query "+name+" created: "+cmd.toString());
        return q;
    }



    
    // This recursive method takes an Expr and breaks it down into a list of subexpressions (literals) based on the logical operators
    

    public static void decomposeExpr(Expr e, Set<Expr> literals) {

        if (ExprHelper.isExprConst(e) || ExprHelper.isExprVar(e)) {
            literals.add(e);
        }
        else if (ExprHelper.isExprUnary(e)) {
            if(ExprHelper.getUnaryOp(e).equals(ExprUnary.Op.NOT)){
                decomposeExpr(ExprHelper.getSub(e), literals); 
            }
            else {
                literals.add(e);
            }
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

    public static List<AbstractionQuery> addAbstractionQueries(List<Expr> items, 
                                                             HashMap<Expr, ExprVar> predVarMap, 
                                                             DashModule d, 
                                                             CompModule c, 
                                                             String name,
                                                             AbstractionQuery.QueryType typ) {

        List<AbstractionQuery> queries = new ArrayList<AbstractionQuery>();
        
        if(items != null){
            for(Expr p: predVarMap.keySet()) {
                List<Expr> queryArgs = new ArrayList<Expr>(items);
                Expr negp = ExprHelper.createNot(p);
                ExprVar v = predVarMap.get(p);
                String qname = name + "_" + ExprHelper.getVarName(v) + "_" + negString;

                queryArgs.add(negp);
                AbstractionQuery q1 = addQueryPred(queryArgs, d, c, qname, typ, p, true);
                queries.add(q1);

                qname = name + "_" + ExprHelper.getVarName(v);            
                queryArgs.remove(negp);
                queryArgs.add(p);
                AbstractionQuery q2 = addQueryPred(queryArgs, d, c, qname, typ, p, false); 
                queries.add(q2);

                q1.setConjugateQuery(q2);
                q2.setConjugateQuery(q1);                   
            }
        }
        return queries;
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
        String rootName = d.getRootName();

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

        HashMap<Expr, ExprVar> predVarMap = new HashMap<Expr, ExprVar>();
        int i = 0;
        for(Expr p: absPreds) {
            //String bvname = DashFQN.fqn(rootName, boolVarString + Integer.toString(i));
            String bvname = boolVarString + Integer.toString(i);
            predVarMap.put(p, ExprHelper.createVar(bvname));
            i += 1;
        }


        List<AbstractionQuery> queries = new ArrayList<AbstractionQuery>(); 
        HashMap<String, List<AbstractionQuery> > transGuardQueryMap = new HashMap<String, List<AbstractionQuery> >();
        HashMap<String, List<AbstractionQuery> > transActionQueryMap = new HashMap<String, List<AbstractionQuery> >();
        HashMap<String, Expr> invMap = new HashMap<String, Expr>();
        HashMap<String, List<AbstractionQuery> > invQueryMap = new HashMap<String, List<AbstractionQuery> >();
        
        if(inits.size() > 0){
            queries.addAll(addAbstractionQueries(inits, predVarMap, d, c, initsString, AbstractionQuery.QueryType.INIT));
        }

        if(invs.size() > 0) {
            i = 0;
            for(Expr inv: invs){
                List<Expr> arg = new ArrayList<Expr>();
                arg.add(inv);
                String invName = invString + Integer.toString(i);
                List<AbstractionQuery> qs = addAbstractionQueries(arg, predVarMap, d, c, invName, AbstractionQuery.QueryType.INV);
                queries.addAll(qs);
                invMap.put(invName, inv);
                invQueryMap.put(invName, qs);
                i += 1;
            }
        }

        
        for(Map.Entry<String, Expr> entry: allTransGuards.entrySet()) {
            Expr g = entry.getValue(); 
            List<Expr> arg = new ArrayList<Expr>();
            arg.add(g);
            String qname = guardString + "_" + DashFQN.translateFQN(entry.getKey());
            List<AbstractionQuery> qs = addAbstractionQueries(arg, predVarMap, d, c, qname, AbstractionQuery.QueryType.GUARD);
            transGuardQueryMap.put(entry.getKey(), qs);
            queries.addAll(qs);
        }

        for(String t: allTransNames) {
            Expr guard = allTransGuards.get(t);
            Expr action = allTransActions.get(t);
            if(guard != null && action != null) {
                List<Expr> arg = new ArrayList<Expr>();
                arg.add(guard);
                arg.add(action);
                String qname = actionString + "_" + DashFQN.translateFQN(t);
                List<AbstractionQuery> qs = addAbstractionQueries(arg, predVarMap, d, c, qname, AbstractionQuery.QueryType.ACTION);
                transActionQueryMap.put(t, qs);
                queries.addAll(qs);
            }
        }
        
        c = MainFunctions.resolveAlloy(c, rep);
        System.out.println("Total number of abstraction queries: "+queries.size());

        String outfilename = inputFilename.substring(0,inputFilename.length()-4) + "-abs-query.als";

        try {
            DashModule d2 = MainFunctions.parseDashFile(inputFilename, rep);                
            d2 = MainFunctions.resolveDash(d2, rep);
            CompModule c2 = MainFunctions.translate(d2, rep);

            File out = new File(outfilename);
            if (!out.exists()) out.createNewFile();
            System.out.println("Creating: " + outfilename);
            FileWriter fw = new FileWriter(out.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(d.toStringAlloy());

            for(AbstractionQuery q: queries) {
                bw.write(q.predBody);
            }

            for(AbstractionQuery q: queries) {
                bw.write(q.cmdBody);
            }
            bw.close();
            System.out.println("Alloy file with abstraction queries created.");    

        }   
        catch (Exception e) {
            System.out.println("Exception: "+e.toString());
        }

        c = MainFunctions.parseAlloyFileAndResolveAll(outfilename, rep);
        List<Command> cmdlist = c.getAllCommands();
        HashMap<String, Boolean> queryResults = new HashMap<String, Boolean>();
        for(Command cmd: cmdlist) {
            A4Options options = new A4Options();
            A4Solution solution = MainFunctions.executeCommand(cmd, c, rep, options);
            queryResults.put(cmd.label, solution.satisfiable());
        }

        for(AbstractionQuery q: queries) {
            q.setResult(queryResults.get(q.commandName));
        }

        HashMap<String, Boolean> processed = new HashMap<String, Boolean>();
        for(AbstractionQuery q: queries) {
            processed.put(q.commandName, false);
        }

        List<Expr> absInits = new ArrayList<Expr>();
        List<Expr> absInvs = new ArrayList<Expr>();
        Expr dshSnap = ExprHelper.createVar(DashStrings.snapshotName);

        for(AbstractionQuery q: queries) {
            if(processed.get(q.commandName) == false) {
                //inits
                if(q.isInitQuery()) {

                    AbstractionQuery qConj = q.conjugate;
                    boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                    boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                    Expr v = predVarMap.get(q.absPred);
                    Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                    Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, dshSnap, vfqn);

                    if(result && !negResult){
                        // add BV as it is
                        absInits.add(ExprHelper.createIsTrue(dvfqn));
                    }
                    else if(!result && negResult) {
                        // add negated BV
                        absInits.add(ExprHelper.createIsFalse(dvfqn));
                    }
                    else {
                        // do nothing
                    }
                    processed.put(q.commandName, true);
                    processed.put(qConj.commandName, true);
                }
            }
        }

        List<Expr> absInit = new ArrayList<Expr>();
        absInit.add(ExprHelper.createAndFromList(absInits));
        
        for(String in: invQueryMap.keySet()) {
            List<Expr> absInvVars = new ArrayList<Expr>();
            for(AbstractionQuery q: invQueryMap.get(in)){
                if(processed.get(q.commandName) == false){

                    AbstractionQuery qConj = q.conjugate;
                    boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                    boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                    ExprVar v = predVarMap.get(q.absPred);
                    Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                    Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, dshSnap, vfqn);

                    if(result && !negResult){
                        // add BV as it is
                        absInvVars.add(ExprHelper.createIsTrue(dvfqn));
                    }
                    else if(!result && negResult) {
                        // add negated BV
                        absInvVars.add(ExprHelper.createIsFalse(dvfqn));
                    }
                    else {
                        // do nothing
                    }
                    processed.put(q.commandName, true);
                    processed.put(qConj.commandName, true);
                }
            }
            Expr absInv = ExprHelper.createAndFromList(absInvVars);
            absInvs.add(absInv);
        }

        HashMap<String, Expr> transAbsGuard = new HashMap<String, Expr>();
        HashMap<String, Expr> transAbsAction = new HashMap<String, Expr>();
        
        //guards 
        for(String t: allTransNames) {
            List<Expr> absVars = new ArrayList<Expr>();
            if(transGuardQueryMap.containsKey(t)){
                for(AbstractionQuery q: transGuardQueryMap.get(t)) {
                    if(processed.get(q.commandName) == false) {

                        AbstractionQuery qConj = q.conjugate;
                        boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                        boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                        Expr v = predVarMap.get(q.absPred);
                        Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                        Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, dshSnap, vfqn);

                        if(result && !negResult){
                            // add BV as it is
                            absVars.add(ExprHelper.createIsTrue(dvfqn));
                        }
                        else if(!result && negResult) {
                            // add negated BV
                            absVars.add(ExprHelper.createIsFalse(dvfqn));
                        }
                        else {
                            // do nothing
                        }
                        processed.put(q.commandName, true);
                        processed.put(qConj.commandName, true);
                    }
                }
            }
            Expr absGuard = ExprHelper.createAndFromList(absVars);
            transAbsGuard.put(t, absGuard);
        }

        //actions 
        Set<String> varsChanged = new HashSet<String>();

        for(String t: allTransNames) {
            List<Expr> absVars = new ArrayList<Expr>();
            if(transActionQueryMap.containsKey(t)){
                for(AbstractionQuery q: transActionQueryMap.get(t)) {
                    if(processed.get(q.commandName) == false) {

                        AbstractionQuery qConj = q.conjugate;
                        boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                        boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                        Expr v = predVarMap.get(q.absPred);
                        Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                        Expr vPrime = ExprHelper.createPrime(vfqn);
                        Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, dshSnap, vPrime);

                        if(result && !negResult){
                            // add BV as it is
                            absVars.add(ExprHelper.createIsTrue(dvfqn));
                            varsChanged.add(ExprHelper.getVarName((ExprVar) vfqn));
                        }
                        else if(!result && negResult) {
                            // add negated BV
                            absVars.add(ExprHelper.createIsFalse(dvfqn));
                            varsChanged.add(ExprHelper.getVarName((ExprVar) vfqn));
                        }
                        else {
                            // do nothing
                        }
                        processed.put(q.commandName, true);
                        processed.put(qConj.commandName, true);
                    }
                }
            }
            Expr absAction = ExprHelper.createAndFromList(absVars);
            transAbsAction.put(t, absAction);
        }

        // add the boolean variables to a new VarTable
        VarTable vt = new VarTable();
        List<String> prms = new ArrayList<String>();
        List<Integer> prmsIdx = new ArrayList<Integer>();
        Expr boolType = ExprHelper.createVar(DashStrings.boolName);
        
        for(ExprVar bv: predVarMap.values()){
            String bvname = ExprHelper.getVarName(bv);
            String bvfqn = DashFQN.translateFQN(DashFQN.fqn(rootName, bvname));
            if(varsChanged.contains(bvfqn)) {
                vt.addVar(bvfqn, DashStrings.IntEnvKind.INT, prms, prmsIdx, boolType);
            }
            else{
                vt.addVar(bvfqn, DashStrings.IntEnvKind.ENV, prms, prmsIdx, boolType);
            }
        }
        
        DashModule absd = MainFunctions.parseDashFile(inputFilename, rep);
        //System.out.println("Parsed Dash file");
        if (absd == null) 
            DashErrors.emptyFile(inputFilename);
                
        absd = MainFunctions.resolveDash(absd, rep); 
        //System.out.println("Resolved Dash");

        absd.stateTable.setInits(absInit);
        absd.stateTable.setInvs(absInvs);

        absd.varTable = vt; 

        for(String t: allTransNames){
            Expr g = transAbsGuard.get(t);
            Expr a = transAbsAction.get(t);
            if(g != null){
                // System.out.println("Testing: Abstract guard...");
                // System.out.println(g.toString());
                absd.setTransWhen(t, transAbsGuard.get(t));
            }
            if(a != null){
                absd.setTransDo(t, transAbsAction.get(t));
            }
            
        }

        

        //vartable varelemt can take empty list for prms
        //invs and inits just run query as inv & pred

        System.out.println("========Abstract Inits==========");
        for(Expr init: absd.stateTable.getInits()) {
            System.out.println(init.toString());
        }
        System.out.println("===================");

        System.out.println("========Abstract Invs==========");
        for(Expr inv: absd.stateTable.getInvs()) {
            System.out.println(inv.toString());
        }
        System.out.println("===================");
        System.out.println("========Abstract State Table==========");
        System.out.println(absd.stateTable.toString());
        System.out.println("===================");

        System.out.println("========Abstract Transition Table==========");
        System.out.println(absd.transTable.toString());
        System.out.println("===================");

        System.out.println("========Abstract Variable Table==========");
        System.out.println(absd.varTable.toString());
        System.out.println("===================");


        // all different snapshot does not allow loop ; make sure not enables

        return absd;
        //return d;
        
    }
}



// abstraction method is conservative; stronger than it needs to be; with regards to reachability
// later: act && inv' not SAT is bad