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
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.alloy4.ConstList;

import java.io.*;
import java.util.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;


public class PredicateAbstraction {

    public final String negString = "neg";
    public final String boolVarString = "B";
    public final String guardString = "guard";
    public final String actionString = "action";
    public final String initsString = "inits";
    public final String invString = "inv";
    public final String propString = "prop";

    public String fileName;
    public DashModule origModel;
    public CompModule origTransAlloy;
    public HashMap<Expr, ExprVar> formulaVarMap;

    public PredicateAbstraction(String inputFilename) {
        
        this.fileName = inputFilename;
        
        A4Reporter rep = new A4Reporter();
        this.origModel = MainFunctions.parseDashFile(fileName, rep);
        System.out.println("Parsed Dash file");
        if (origModel == null) 
            DashErrors.emptyFile(inputFilename);
                
        this.origModel = MainFunctions.resolveDash(this.origModel, rep);
        System.out.println("Resolved Dash"); 

        this.origTransAlloy = MainFunctions.translate(this.origModel, rep);
        System.out.println("Translated Dash to Alloy"); 
    }

    /*
        Creates a predicate:

        pred query_tfqn_bv_neg[s, sn: DshSnapshot] {
            sn = s.DshSnapshot/next
            tfqn_guard
            tfqn_action
            abs_pred
        }
    */
    public AbstractionQuery addQueryPred(List<Expr> args, String name, AbstractionQuery.QueryType typ, Expr pred, Boolean neg) {

        List<Expr> body = new ArrayList<Expr>();
        Expr svar = Common.curVar();

        AbstractionQuery q = new AbstractionQuery(name, name, typ, pred, neg);

        if(typ == AbstractionQuery.QueryType.ACTION) {
            List<Decl> snapshots = Common.curNextDecls();
            body.add(ExprHelper.createPredCall(DashStrings.smallStepName, Common.curNextVars()));

            for(Expr e: args) {
                body.add(Common.translateExpr(e, origModel));
            }

            String predBody = origModel.addPredSimple(name, Common.curNextDecls(), body);
            q.setPredBody(predBody);
        }
        else {
            if(typ == AbstractionQuery.QueryType.INIT) {
                List<Expr> curvar = new ArrayList<Expr>();
                curvar.add(Common.curVar());
                body.add(ExprHelper.createPredCall(DashStrings.initFactName, curvar));
            }
            for(Expr e: args) {
                body.add(Common.translateExpr(e, origModel));
            }
            List<Decl> snapshot = new ArrayList<Decl>();
            snapshot.add(Common.curDecl());
            String predBody = origModel.addPredSimple(name, snapshot, body);
            q.setPredBody(predBody);
        }

        boolean check = false;
        Command cmd = CommandHelper.createCommand(origTransAlloy, check, 4, 4, name);
        q.setCommand(cmd);
        q.setCmdBody(cmd.toString() + "\n");
        // System.out.println("Query "+name+" created: "+cmd.toString());
        return q;
    }
    
    // This recursive method takes an Expr and breaks it down into a list of subexpressions (literals) based on the logical operators
    
    public void decomposeExpr(Expr e, Set<Expr> literals) {

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

    public List<AbstractionQuery> addAbstractionQueries(List<Expr> items, String name, AbstractionQuery.QueryType typ) {

        List<AbstractionQuery> queries = new ArrayList<AbstractionQuery>();
        
        if(items != null){
            for(Expr p: formulaVarMap.keySet()) {
                List<Expr> queryArgs = new ArrayList<Expr>(items);
                Expr negp = ExprHelper.createNot(p);
                ExprVar v = formulaVarMap.get(p);
                String qname = name + "_" + ExprHelper.getVarName(v) + "_" + negString;

                queryArgs.add(negp);
                AbstractionQuery q1 = addQueryPred(queryArgs, qname, typ, p, true);
                queries.add(q1);

                qname = name + "_" + ExprHelper.getVarName(v);            
                queryArgs.remove(negp);
                queryArgs.add(p);
                AbstractionQuery q2 = addQueryPred(queryArgs, qname, typ, p, false); 
                queries.add(q2);

                q1.setConjugateQuery(q2);
                q2.setConjugateQuery(q1);                   
            }
        }
        return queries;
    }

    public HashMap<String, Expr> createTransitionGuardMap() {
        
        List<String> allTransNames = origModel.getAllTransNames();
        HashMap<String, Expr> allTransGuards = new HashMap<String, Expr>();

        for(String t: allTransNames){
            Expr g = origModel.getTransWhen(t);
            if(g != null) { 
                allTransGuards.put(t, g);
            }
        }
        return allTransGuards;
    }

    public HashMap<String, Expr> createTransitionActionMap() {
        
        List<String> allTransNames = origModel.getAllTransNames();
        HashMap<String, Expr> allTransActions = new HashMap<String, Expr>();

        for(String t: allTransNames){
            Expr a = origModel.getTransDo(t);
            if(a != null) { 
                allTransActions.put(t, a);
            }
        }
        return allTransActions;
    }

    public void createFormulaVariableMap() {
        
        //get all the transition names, guards, and actions store in a list
        List<String> allTransNames = origModel.getAllTransNames();
        HashMap<String, Expr> allTransGuards = createTransitionGuardMap();
        HashMap<String, Expr> allTransActions = createTransitionActionMap();

        List<Expr> inits = origModel.getInits();
        List<Expr> invs = origModel.getInvs();
        String rootName = origModel.getRootName();

        //for now, if a model has no guards, we do not abstract the model.
        if(allTransGuards.isEmpty() && invs.size() == 0){
            formulaVarMap = new HashMap<Expr, ExprVar>();
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

        formulaVarMap = new HashMap<Expr, ExprVar>();
        int i = 0;
        for(Expr p: absPreds) {
            //String bvname = DashFQN.fqn(rootName, boolVarString + Integer.toString(i));
            String bvname = boolVarString + Integer.toString(i);
            formulaVarMap.put(p, ExprHelper.createVar(bvname));
            i += 1;
        }
    }
     
    // This method takes a DashModule object as input and returns the abstract model

    public DashModule createAbstractModel() {

        // Step 1: Parse, resolve, and translate input Dash file

        A4Reporter rep = new A4Reporter();
        int cmdCtr = origTransAlloy.getAllCommands().size();

        // Step 2: Extract predicates from the guards and invariants and map each predicate to a new abstract boolean variable
        List<String> allTransNames = origModel.getAllTransNames();
        HashMap<String, Expr> allTransGuards = createTransitionGuardMap();
        HashMap<String, Expr> allTransActions = createTransitionActionMap();
        List<Expr> inits = origModel.getInits();
        List<Expr> invs = origModel.getInvs();
        String rootName = origModel.getRootName();
        createFormulaVariableMap();

        if(formulaVarMap == null) {
            System.out.println("The given Dash+ model does not have any guards or invariants (sources of predicates)");
            return origModel;
        }

        // Step 3: Create abstraction Alloy queries (commands to run predicates to abstract Alloy expressions in the Dash Model)

        List<AbstractionQuery> queries = new ArrayList<AbstractionQuery>(); 
        HashMap<String, List<AbstractionQuery> > transGuardQueryMap = new HashMap<String, List<AbstractionQuery> >();
        HashMap<String, List<AbstractionQuery> > transActionQueryMap = new HashMap<String, List<AbstractionQuery> >();
        HashMap<String, Expr> invMap = new HashMap<String, Expr>();
        HashMap<String, List<AbstractionQuery> > invQueryMap = new HashMap<String, List<AbstractionQuery> >();
        
        // Abstract the initial conditions
        if(inits.size() > 0){
            queries.addAll(addAbstractionQueries(inits, initsString, AbstractionQuery.QueryType.INIT));
        }

        // Abstract the invariants separately and individually
        if(invs.size() > 0) {
            int i = 0;
            for(Expr inv: invs){
                List<Expr> arg = new ArrayList<Expr>();
                arg.add(inv);
                String invName = invString + Integer.toString(i);
                List<AbstractionQuery> qs = addAbstractionQueries(arg, invName, AbstractionQuery.QueryType.INV);
                queries.addAll(qs);
                invMap.put(invName, inv);
                invQueryMap.put(invName, qs);
                i += 1;
            }
        }

        // Abstract the transition guards
        for(Map.Entry<String, Expr> entry: allTransGuards.entrySet()) {
            Expr g = entry.getValue(); 
            List<Expr> arg = new ArrayList<Expr>();
            arg.add(g);
            String qname = guardString + "_" + DashFQN.translateFQN(entry.getKey());
            List<AbstractionQuery> qs = addAbstractionQueries(arg, qname, AbstractionQuery.QueryType.GUARD);
            transGuardQueryMap.put(entry.getKey(), qs);
            queries.addAll(qs);
        }

        // Abstract the transition actions
        for(String t: allTransNames) {
            Expr guard = allTransGuards.get(t);
            Expr action = allTransActions.get(t);
            if(guard != null && action != null) {
                List<Expr> arg = new ArrayList<Expr>();
                arg.add(guard);
                arg.add(action);
                String qname = actionString + "_" + DashFQN.translateFQN(t);
                List<AbstractionQuery> qs = addAbstractionQueries(arg, qname, AbstractionQuery.QueryType.ACTION);
                transActionQueryMap.put(t, qs);
                queries.addAll(qs);
            }
        }
        
        // Step 4: Run the abstraction query commands and store the results
        origTransAlloy = MainFunctions.resolveAlloy(origTransAlloy, rep);
        System.out.println("Total number of abstraction queries: "+queries.size());

        String outfilename = fileName.substring(0,fileName.length()-4) + "-abs-query.als";

        try {
            DashModule d2 = MainFunctions.parseDashFile(fileName, rep);                
            d2 = MainFunctions.resolveDash(d2, rep);
            CompModule c2 = MainFunctions.translate(d2, rep);

            File out = new File(outfilename);
            if (!out.exists()) out.createNewFile();
            System.out.println("Creating: " + outfilename);
            FileWriter fw = new FileWriter(out.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(origModel.toStringAlloy());

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

        CompModule c = MainFunctions.parseAlloyFileAndResolveAll(outfilename, rep);

        List<Command> cmdlist = c.getAllCommands();
        HashMap<String, Boolean> queryResults = new HashMap<String, Boolean>();
        try {
            for(Command cmd: cmdlist) {
                A4Options options = new A4Options();
                A4Solution solution = MainFunctions.executeCommand(cmd, c, rep, options);
                queryResults.put(cmd.label, solution.satisfiable());
            }
        }
        catch (Exception e) {
            System.out.println("Exception: "+e.toString());
        }

        for(AbstractionQuery q: queries) {
            q.setResult(queryResults.get(q.commandName));
        }

        // Step 5: Use the results of the queries to abstract the inits, invariants, guards, and actions

        HashMap<String, Boolean> processed = new HashMap<String, Boolean>();
        for(AbstractionQuery q: queries) {
            processed.put(q.commandName, false);
        }

        List<Expr> absInits = new ArrayList<Expr>();
        List<Expr> absInvs = new ArrayList<Expr>();
        Expr dshSnap = ExprHelper.createVar(DashStrings.snapshotName);

        // Abstract the initial conditions
        for(AbstractionQuery q: queries) {
            if(processed.get(q.commandName) == false) {
                //inits
                if(q.isInitQuery()) {

                    AbstractionQuery qConj = q.conjugate;
                    boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                    boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                    Expr v = formulaVarMap.get(q.absPred);
                    Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                    Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, Common.curVar(), vfqn);

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
        if(! absInits.isEmpty()){
            absInit.add(ExprHelper.createAndFromList(absInits));
        }
        
        // Abstract the invariants
        for(String in: invQueryMap.keySet()) {
            List<Expr> absInvVars = new ArrayList<Expr>();
            for(AbstractionQuery q: invQueryMap.get(in)){
                if(processed.get(q.commandName) == false){

                    AbstractionQuery qConj = q.conjugate;
                    boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                    boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                    ExprVar v = formulaVarMap.get(q.absPred);
                    Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                    Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, Common.curVar(), vfqn);

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
            if(!absInvVars.isEmpty()){
                Expr absInv = ExprHelper.createAndFromList(absInvVars);
                absInvs.add(absInv);
            }
            
        }

        HashMap<String, Expr> transAbsGuard = new HashMap<String, Expr>();
        HashMap<String, Expr> transAbsAction = new HashMap<String, Expr>();
        
        // Abstract the transition guards 
        for(String t: allTransNames) {
            List<Expr> absVars = new ArrayList<Expr>();
            if(transGuardQueryMap.containsKey(t)){
                for(AbstractionQuery q: transGuardQueryMap.get(t)) {
                    if(processed.get(q.commandName) == false) {

                        AbstractionQuery qConj = q.conjugate;
                        boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                        boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                        Expr v = formulaVarMap.get(q.absPred);
                        Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                        Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, Common.curVar(), vfqn);

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
            if(!absVars.isEmpty()) {
                Expr absGuard = ExprHelper.createAndFromList(absVars);
                transAbsGuard.put(t, absGuard);
            } 
        }

        // Abstract the transition actions 
        Set<String> varsChanged = new HashSet<String>();

        for(String t: allTransNames) {
            List<Expr> absVars = new ArrayList<Expr>();
            if(transActionQueryMap.containsKey(t)){
                for(AbstractionQuery q: transActionQueryMap.get(t)) {
                    if(processed.get(q.commandName) == false) {

                        AbstractionQuery qConj = q.conjugate;
                        boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                        boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                        Expr v = formulaVarMap.get(q.absPred);
                        Expr vfqn = ExprHelper.createVar(DashFQN.translateFQN(DashFQN.fqn(rootName, ExprHelper.getVarName((ExprVar) v))));
                        //Expr vPrime = ExprHelper.createPrime(vfqn);
                        //Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, Common.nextVar(), vPrime);
                        Expr dvfqn = ExprHelper.createJoin(Pos.UNKNOWN, Common.nextVar(), vfqn);

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
            if(!absVars.isEmpty()) {
                Expr absAction = ExprHelper.createAndFromList(absVars);
                transAbsAction.put(t, absAction);
            }
        }

        // Step 6: Add the abstract boolean variables to a new VarTable
        VarTable vt = new VarTable();
        List<String> prms = new ArrayList<String>();
        List<Integer> prmsIdx = new ArrayList<Integer>();
        Expr boolType = ExprHelper.createVar(DashStrings.boolName);
        
        for(ExprVar bv: formulaVarMap.values()){
            String bvname = ExprHelper.getVarName(bv);
            String bvfqn = DashFQN.translateFQN(DashFQN.fqn(rootName, bvname));
            if(varsChanged.contains(bvfqn)) {
                vt.addVar(bvfqn, DashStrings.IntEnvKind.INT, prms, prmsIdx, boolType);
            }
            else{
                vt.addVar(bvfqn, DashStrings.IntEnvKind.ENV, prms, prmsIdx, boolType);
            }
        }
        
        // Step 7: Create the abstract DashModule by re-parsing and resolving the input file and replacing the 
        // inits, invs, guards, and actions with their corresponding abstract versions

        DashModule absd = MainFunctions.parseDashFile(fileName, rep);
        if (absd == null) 
            DashErrors.emptyFile(fileName);
                
        absd = MainFunctions.resolveDash(absd, rep); 

        absd.stateTable.setInits(absInit);
        absd.stateTable.setInvs(absInvs);

        absd.varTable = vt; 

        for(String t: allTransNames){
            Expr g = transAbsGuard.get(t);
            Expr a = transAbsAction.get(t);
            if(g != null){
                absd.setTransWhen(t, transAbsGuard.get(t));
            }
            else {
                absd.setTransWhen(t, null);
            }
            if(a != null){
                absd.setTransDo(t, transAbsAction.get(t));
            }
            else {
                absd.setTransDo(t, null);
            }
            
        }

        // Step 8: Print the tables of the abstract model
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
    }

    /*
    public static void createAbstractProperty(String propFilename, DashModule absd) {
        
        A4Reporter rep = new A4Reporter();
        DashModule d = MainFunctions.parseDashFile(fileName, rep);
        if (d == null) 
            DashErrors.emptyFile(fileName);
                
        String propBody = new String();
        try{
            FileReader fr = new FileReader(propFilename);
            BufferedReader br = new BufferedReader(fr);

            while(line != null) {
                d.alloyString += (line + "\n");
                propBody += (line + "\n");
            }
            br.close();
            fr.close();
        }
        catch (Exception e) {
            System.out.println("Exception: "+e.toString());
        } 

        d = MainFunctions.resolveDash(d, rep);
        CompModule c = MainFunctions.translate(d, rep);

        String rootName = d.getRootName();

        // trying to get all funcs without resolving alloy
        int index = c.getAllFunc().size() - 1;
        Func propFunc = c.getAllFunc().get(index);
        Expr propBody = propFunc.getBody();
        String propLabel = propFunc.label;
        List<Expr> propList = new ArrayList<Expr>();
        propList.add(propBody);

        index = c.getAllCommands().size() - 1;
        Command propCmd = c.getAllCommands().get(index);

        List<AbstractionQuery> queries = new ArrayList<AbstractionQuery>(); 
        String queryName = (propLabel.length() > 0)? propString + "_" + propLabel: propString;
        queries.addAll(addAbstractionQueries(propList, queryName, AbstractionQuery.QueryType.PROPERTY));

        //execute abstraction queries to abstract the property

        c = MainFunctions.resolveAlloy(c, rep);
        System.out.println("Total number of abstraction queries: "+queries.size());

        String outfilename = propFilename.substring(0,propFilename.length()-4) + "-abs-query.als";

        try {
            DashModule d2 = MainFunctions.parseDashFile(fileName, rep);                
            d2 = MainFunctions.resolveDash(d2, rep);
            CompModule c2 = MainFunctions.translate(d2, rep);

            File out = new File(outfilename);
            if (!out.exists()) out.createNewFile();
            System.out.println("Creating: " + outfilename);
            FileWriter fw = new FileWriter(out.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(origModel.toStringAlloy());

            for(AbstractionQuery q: queries) {
                bw.write(q.predBody);
            }

            for(AbstractionQuery q: queries) {
                bw.write(q.cmdBody);
            }
            bw.close();
            System.out.println("Alloy file with abstraction queries for the property in "+ propFilename +" created.");    

        }   
        catch (Exception e) {
            System.out.println("Exception: "+e.toString());
        }

        c = MainFunctions.parseAlloyFileAndResolveAll(outfilename, rep);

        List<Command> cmdlist = c.getAllCommands();
        HashMap<String, Boolean> queryResults = new HashMap<String, Boolean>();
        try {
            for(Command cmd: cmdlist) {
                A4Options options = new A4Options();
                A4Solution solution = MainFunctions.executeCommand(cmd, c, rep, options);
                queryResults.put(cmd.label, solution.satisfiable());
            }
        }
        catch (Exception e) {
            System.out.println("Exception: "+e.toString());
        }

        for(AbstractionQuery q: queries) {
            q.setResult(queryResults.get(q.commandName));
        }

        // construct the abstract property

        HashMap<String, Boolean> processed = new HashMap<String, Boolean>();
        for(AbstractionQuery q: queries) {
            processed.put(q.commandName, false);
        }

        List<Expr> absProp = new ArrayList<Expr>();
        Expr dshSnap = ExprHelper.createVar(DashStrings.snapshotName);

        for(AbstractionQuery q: queries) {
            if(processed.get(q.commandName) == false) {
                //inits
                if(q.isPropertyQuery()) {

                    AbstractionQuery qConj = q.conjugate;
                    boolean result = (q.isQueryNegatedPredicate())? q.result : qConj.result;
                    boolean negResult = (q.isQueryNegatedPredicate())? qConj.result : q.result;
                    Expr v = formulaVarMap.get(q.absPred);
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

        Expr absPropBody = ExprHelper.createAndFromList(absProp);

    }*/
}



// abstraction method is conservative; stronger than it needs to be; with regards to reachability
// later: act && inv' not SAT is bad