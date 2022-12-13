package org.alloytools.dash.core;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThrows;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import ca.uwaterloo.watform.ast.DashConcState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashValidation;

public class DashModelsTest {
	
    //Dash Parser Unit Tests
    @Test
    public void testStates() throws Exception {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashOptions.isElectrum = false;

        assertNotNull(module.getORStates().get("concState_topStateA"));
        assertNotNull(module.getORStates().get("concState_topStateA_innerState"));
        assertNotNull(module.getORStates().get("concState_topStateB"));
        assertEquals(module.getORStates().get("concState_topStateA").getInnerORStates().get(0).getRawName(), "innerState");
        DashValidation.clearContainers();
    }

    @Test
    public void testConcStates() throws Exception {

        String dashModel = "conc state topConcStateA { conc state innerConcState{  default state A {} } } conc state topConcStateB { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateA").getRawName().equals("topConcStateA")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateA").getInnerConcStates().get(0).getRawName().equals("innerConcState")))
            throw new Exception("Child concurrent state not stored in the IDS");
        if (!(coreDashModule.getORStates().get("topConcStateA_innerConcState_A").getRawName().equals("A")))
            throw new Exception("Inner OR state not stored in the IDS");
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateB").getRawName().equals("topConcStateB")))
            throw new Exception("Top level concurrent state not stored in the IDS");

        DashValidation.clearContainers();
    }
     
    @Test
    public void testParamConcStates() throws Exception { 

        String dashModel = "conc state topConcStateA [PID1] { default state A {} } conc state topConcStateB [PID2] { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateA").getRawName().equals("topConcStateA")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateB").getRawName().equals("topConcStateB")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateA").getReplicatedIdentifier().equals("PID1")))
            throw new Exception("Top level concurrent (topConcStateA) parameter not stored properly." + " Param: " + module.getAllConcurrentStates().get("topConcStateA").getReplicatedIdentifier());
        if (!(coreDashModule.getAllConcurrentStates().get("topConcStateB").getReplicatedIdentifier().equals("PID2")))
            throw new Exception("Top level concurrent (topConcStateB) parameter not stored properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testVarRefs() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		var1: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					one p: PID2 | Child2[p]/var2' = {none}\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		var2: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {\n"
        		+ "					one p: PID1 | Child1[p]/var1' = {none}\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        DashOptions.isElectrum = false;
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = module.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = module.funcs.get(name);
        }
         
        String expectedOutput1 = "(one p | p.s_next . Parent_Child2_var2 = none)";
        String expectedOutput2 = "(one p | p.s_next . Parent_Child1_var1 = none)";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
   
    @Test
    public void testTransitions() throws Exception {

        String dashModel = "conc state topConcStateA { event A{} trans A {on A goto B} default state B {trans B {on A}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
 
        if (!(coreDashModule.transitions.get("topConcStateA_A").getRawName().equals("A")))
            throw new Exception("Transition not stored in the IDS");
        if (!(coreDashModule.transitions.get("topConcStateA_B_B").getRawName().equals("B")))
            throw new Exception("Transition not stored in the IDS");
        if (!(coreDashModule.transitions.get("topConcStateA_A").getDestination().getAllDestinations().get(0).equals("topConcStateA_B")))
            throw new Exception("Transition goto not stored in the IDS" + " Expected: " + coreDashModule.transitions.get("topConcStateA_A").getDestination().getAllDestinations().get(0));
        if (!(coreDashModule.transitions.get("topConcStateA_B_B").getTriggerEvent().getRawName().equals("topConcStateA_A")))
            throw new Exception("Transition event not stored in the IDS");

        DashValidation.clearContainers();
    }

    @Test
    public void testVarNames() throws Exception {

        String dashModel = "conc state concState { var_one: none->none var_two: none->none conc state innerConcState {var_three: none->none} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashOptions.isElectrum = false;

        if (!module.getRawVarNames().get("concState").get(0).equals("var_one"))
            throw new Exception("Outer Conc State variable not stored properly.");
        if (!module.getRawVarNames().get("concState").get(1).equals("var_two"))
            throw new Exception("Outer Conc State variable not stored properly.");
        if (!module.getRawVarNames().get("concState_innerConcState").get(0).equals("var_three"))
            throw new Exception("Inner Conc State variable not stored properly.");

        DashValidation.clearContainers();
    }


    //CoreDash Unit Tests
     @Test
    public void testCoreDashTransitions() throws Exception {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.transitions.values())
            transitions.add(trans);

        if (transitions.size() < 3)
            throw new Exception("Every transition has not been stored." + " Count: " + transitions.size());
        if (transitions.size() > 3)
            throw new Exception("More transitions than necessary has been stored.");
        if (!transitions.get(0).getFullyQualName().equals("concState_t_1"))
            throw new Exception("Transition Name not stored correctly.");
        if (!transitions.get(1).getFullyQualName().equals("concState_trans_two"))
            throw new Exception("Transition Name not stored correctly.");
        if (!transitions.get(2).getFullyQualName().equals("concState_state_one_t_2"))
            throw new Exception("Transition Name not stored correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionIncompleteCommand() throws Exception {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.transitions.values()) {
            transitions.add(trans);
        }

        if (transitions.size() < 3)
            throw new Exception("Every transition has not been stored.");
        if (transitions.size() > 3)
            throw new Exception("More transitions than necessary has been stored.");

        if (!transitions.get(0).getOrigin().getAllOrigins().get(0).equals("concState"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).getDestination().getAllDestinations().get(0).equals("concState"))
            throw new Exception("Transition Goto Expr not stored correctly.");

        if (!transitions.get(1).getOrigin().getAllOrigins().get(0).equals("concState"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).getOrigin().getAllOrigins().get(0).equals("concState"))
            throw new Exception("Transition Goto Expr not stored correctly.");

        if (!transitions.get(2).getOrigin().getAllOrigins().get(0).equals("concState/state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(2).getOrigin().getAllOrigins().get(0).equals("concState/state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");


        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionAllCommands() throws Exception {

        String dashModel = "conc state concState { var_one: none event event_one {} default state state_one {} state state_two {} trans {from state_one, state_two on event_one when var_one = none do var_one' = var_one goto state_two send event_one }}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.transitions.values()) {
            transitions.add(trans);
        }

        if (!transitions.get(0).getOrigin().getAllOrigins().get(0).equals("concState_state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).getTriggerEvent().getRawName().equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(0).getAction().getAllExpression().get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(0).getCondition().getAllExpressions().get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly. Expected is: var_one = none, Actual is: " + transitions.get(0).getCondition().getAllExpressions().get(0).toString());
        if (!transitions.get(0).getDestination().getAllDestinations().get(0).equals("concState_state_two"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).getEventsTriggered().getRawName().equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).getOrigin().getAllOrigins().get(0).equals("concState_state_two"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).getTriggerEvent().getRawName().equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(1).getAction().getAllExpression().get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(1).getCondition().getAllExpressions().get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly. Expected is: var_one = none, Actual is: " + transitions.get(1).getCondition().getAllExpressions().get(0).toString());
        if (!transitions.get(1).getDestination().getAllDestinations().get(0).equals("concState_state_two"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).getEventsTriggered().getRawName().equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionTemplate() throws Exception {

        String dashModel = "conc state concState { var_one: none event event_one {} def trans template [s: State, e: Event] {from s, state_two on e when var_one = none do var_one' = var_one goto s send e} default state state_one {} state state_two {} trans{ template[state_one, event_one]} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.transitions.values()) {
            transitions.add(trans);
        }

        if (!transitions.get(0).getOrigin().getAllOrigins().get(0).equals("concState_state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).getTriggerEvent().getRawName().equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(0).getAction().getAllExpression().get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(0).getCondition().getAllExpressions().get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly.");
        if (!transitions.get(0).getDestination().getAllDestinations().get(0).equals("concState_state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).getEventsTriggered().getRawName().equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).getOrigin().getAllOrigins().get(0).equals("concState_state_two"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).getTriggerEvent().getRawName().equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(1).getAction().getAllExpression().get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(1).getCondition().getAllExpressions().get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly.");
        if (!transitions.get(1).getDestination().getAllDestinations().get(0).equals("concState_state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).getEventsTriggered().getRawName().equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

    //CoreDash to Alloy AST Unit Tests
    @Test
    public void testPredicateNames() throws Exception {

        String dashModel = "conc state topConcStateA { event envA{} trans A {on envA goto B} default state B {trans B {on envA}} }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        if (!(coreDashModule.funcs.keySet().contains("pre_topConcStateA_A")))
            throw new Exception("Pre-Condition Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("pos_topConcStateA_A")))
            throw new Exception("Post-Condition Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("topConcStateA_A")))
            throw new Exception("Trans Name Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("semantics_topConcStateA_A")))
            throw new Exception("Semantics Predicate Not Stored Correctly.");

        if (!(coreDashModule.funcs.keySet().contains("pre_topConcStateA_B_B")))
            throw new Exception("Pre-Condition Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("pos_topConcStateA_B_B")))
            throw new Exception("Post-Condition Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("topConcStateA_B_B")))
            throw new Exception("Trans Name Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("semantics_topConcStateA_B_B")))
            throw new Exception("Semantics Predicate Not Stored Correctly.");

        if (!(coreDashModule.funcs.keySet().contains("init")))
            throw new Exception("Init Predicate Not Stored Correctly.");
        if (!(coreDashModule.funcs.keySet().contains("small_step")))
            throw new Exception("small_step Name Predicate Not Stored Correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testSignatureNames() throws Exception {
        String dashModel = "conc state topConcStateA { event envA{} trans A {on envA goto B} default state B {trans B {on envA}} }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        if (!(coreDashModule.sigs.keySet().contains("Snapshot")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("SystemState")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("topConcStateA")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("topConcStateA_B")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("topConcStateA_envA")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("topConcStateA_A")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(coreDashModule.sigs.keySet().contains("topConcStateA_B_B")))
            throw new Exception("Signature Name Not Stored Correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testPreCondPred() throws Exception {
        String dashModel = "conc state concState { var_one: none event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("pre_concState_A"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[concState_stateA in s.conf0, concState_envA in s.events0 & EnvironmentEvent, s . concState_var_one = none]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Pre-Conditions Not Stored Properly." + " Actual: " + funcs.get(0).getBody().toString());

        DashValidation.clearContainers();
    }

    @Test
    public void testPosCondPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;
        
        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("pos_concState_A"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[s_next.conf0 = s.conf0 - concState_stateA + concState_stateA, s_next.concState_var_one = s.concState_var_one, no s_next.events0 & InternalEvent]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString())) {
            throw new Exception("Post-Conditions Not Stored Properly. Expected: " + expectedOutput + " Actual: " + funcs.get(0).getBody().toString());
        }

        DashValidation.clearContainers();
    }
    
    
    @Test
    public void testPosCondPredWithHierarchy() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("pos_concState_inner_A"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[s_next.conf0 = s.conf0 - concState_inner_stateA + concState_inner_stateA, s_next.concState_var_one = s.concState_var_one, (none.concState_inner_A.s_next.s.testIfNextStable0 => AND[s_next.stable = True, (s.stable = True => s_next.events0 & InternalEvent = none else s_next.events0 & InternalEvent = s.events0 & InternalEvent)] else AND[s_next.stable = False, (s.stable = True => AND[s_next.events0 & InternalEvent = none, s_next.events0 & EnvironmentEvent = s.events0 & EnvironmentEvent] else s_next.events0 = s.events0)])]";
        
        if (!expectedOutput.equals(funcs.get(0).getBody().toString())) {
            throw new Exception("Post-Conditions Not Stored Properly. Expected: " + expectedOutput + " Actual: " + funcs.get(0).getBody().toString());
        }

        DashValidation.clearContainers();
    }
    
    //@Test
    public void testVarRefConstraints() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		var1: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					var1' = {none}\n"
        		+ "					one p: PID2 | Child2[p]/var2' = {none}\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		var2: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					var2' = {none}\n"
        		+ "					one p: PID1 | Child1[p]/var1' = {none}\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = coreDashModule.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = coreDashModule.funcs.get(name);
        }
         
        String expectedOutput1 = "(all quant | quant . s_next.Parent_Child2_var2 = quant . s.Parent_Child2_var2)]), (all quant | quant.s_next.Parent_Child1_var1 = quant.s.Parent_Child1_var1)";
        String expectedOutput2 = "(all quant | quant . s_next.Parent_Child1_var1 = quant . s.Parent_Child1_var1)]), (all quant | quant.s_next.Parent_Child2_var2 = quant.s.Parent_Child2_var2)";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
    //@Test
    public void testBufferInPostCond() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		buf1: buf[PID1]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					buf1.add[this]\n"
        		+ "					one p: PID2 | Child2[p]/buf2.add[p]\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		buf2: buf[PID2]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					buf2.add[this]\n"
        		+ "					one p: PID1 | Child1[p]/buf1.add[p]\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = coreDashModule.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = coreDashModule.funcs.get(name);
        }
         
        String expectedOutput1 = "p.p.s_next.Parent_Child1_buf1.p.s . Parent_Child1_buf1.add, (one p | AND[p.p.s_next.Parent_Child2_buf2.p.s.Parent_Child2_buf2.add, (all quant | quant . s_next.Parent_Child2_buf2 = quant . s.Parent_Child2_buf2)]), (all quant | quant.s_next.Parent_Child1_buf1 = quant.s.Parent_Child1_buf1)";
        String expectedOutput2 = "p.p.s_next.Parent_Child2_buf2.p.s . Parent_Child2_buf2.add, (one p | AND[p.p.s_next.Parent_Child1_buf1.p.s.Parent_Child1_buf1.add, (all quant | quant . s_next.Parent_Child1_buf1 = quant . s.Parent_Child1_buf1)]), (all quant | quant.s_next.Parent_Child2_buf2 = quant.s.Parent_Child2_buf2)";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testBufferDataStructure() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		buf1: buf[PID1]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					buf1.add[this]\n"
        		+ "					one p: PID2 | Child2[p]/buf2.add[p]\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		buf2: buf[PID2]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					buf2.add[this]\n"
        		+ "					one p: PID1 | Child1[p]/buf1.add[p]\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        //DashModule coreDash = DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        //DashModule alloy = new CoreDashToAlloy().convertToAlloyAST(coreDash);
              
        List<String> buffers = new ArrayList<String>();
        List<String> bufferElems = new ArrayList<String>();
        DashOptions.isElectrum = false;
        
        for (String name : module.getBufferElement().keySet()) {
        	buffers.add(name);
        	bufferElems.add(module.getBufferElement().get(name));
        }
         
        if (!(buffers.get(0).equals("Parent_Child1_buf1")))
            throw new Exception("Buffer Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(buffers.get(1).equals("Parent_Child2_buf2")))
            throw new Exception("Buffer Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(bufferElems.get(0).equals("PID1")))
            throw new Exception("Buffer Element Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(bufferElems.get(1).equals("PID2")))
            throw new Exception("Buffer Element Not Stored Properly." + " Expected: " + buffers.get(0));
        
        
        DashValidation.clearContainers();
    } 
    
    
    @Test
    public void testEnabledAfterNextStep() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("enabledAfterStep_concState_inner_A"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[concState_inner_stateA in s.conf0, s . concState_var_one = none, (_s.stable = True => AND[no t & concState_inner_A + concState_inner_B, concState_envA in _s.events0 & EnvironmentEvent + genEvents] else AND[no _s.taken0 + t & concState_inner_A + concState_inner_B, concState_envA in _s.events0 + genEvents])]";
        
        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Enabled After Not Stored Properly." + " Expected: " + funcs.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testTestIfNextStep() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("testIfNextStable0"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[! genEvents.t.s_next.s.enabledAfterStep_concState_inner_A, ! genEvents.t.s_next.s.enabledAfterStep_concState_inner_B]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("TestIfNext After Not Stored Properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testSemanticsPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("semantics_concState_A"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "s_next.taken0 = concState_A";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Semantics Not Stored Properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testInitPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        List<Func> funcs = new ArrayList<Func>();

        for (String name : coreDashModule.funcs.keySet()) {
            if (name.equals("init"))
                funcs = coreDashModule.funcs.get(name);
        }

        String expectedOutput = "AND[s.conf0 = concState_stateA, no s.taken0, no s.events0 & InternalEvent]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Init Not Stored Properly.");

        DashValidation.clearContainers();
    }


    @Test
    public void testModelFactTraces() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        String expectedOutput = "AND[snapshot/first.init, (all s | ! s in snapshot/last => s . next.s.small_step), (all s | AND[! s in snapshot/last, ! s . next.s.small_step] => s . next.s.equals)]";

        if (!expectedOutput.equals(coreDashModule.facts.get(0).b.toString()))
            throw new Exception("Fact Not Stored Properly." + " Actual: " + coreDashModule.facts.get(0).b.toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testModelFactCTL() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = true;
        DashOptions.generateTraces = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        String expectedOutput = "AND[(all s | s in ks_s0 <=> s.init), (all s,s_next | s -> s_next in ks_sigma <=> s_next.s.small_step)]";
        
        if (!expectedOutput.equals(coreDashModule.facts.get(2).b.toString()))
        	throw new Exception("Fact Not Stored Properly." + " Actual: " + coreDashModule.facts.get(2).b.toString());

        DashValidation.clearContainers();
    }
    
    // Unit Testing For The Dynamic Approach
    @Test
    public void testRepStateNestedInRepState() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "	conc state C {\n"
        		+ "		default state S0 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state R1 [IE1] {\n"
        		+ "		default state S0 {}\n"
        		+ "		state S1 {\n"
        		+ "			conc state R2 [IE2] {\n"
        		+ "				default state S0 {}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		trans T0 {\n"
        		+ "			from S0\n"
        		+ "			goto S1\n"
        		+ "		}\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        DashOptions.isElectrum = false;

        if (!alloyModule.getConcurrentStateNames().contains("R0")) {
        	throw new Exception("Replicated Concurrent State Not Stored Properly.");
        }
        if (!alloyModule.getConcurrentStateNames().contains("R0_R1")) {
        	throw new Exception("Replicated Concurrent State Not Stored Properly.");
        }
        if (!alloyModule.getConcurrentStateNames().contains("R0_R1_S1_R2")) {
        	throw new Exception("Replicated Concurrent State Not Stored Properly.");
        }

        DashValidation.clearContainers();
    }
    
    // Check if we have the conf1, conf2 and conf3 relations
    @Test
    public void testNestedConfRelNames() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "	conc state C {\n"
        		+ "		default state S0 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state R1 [IE1] {\n"
        		+ "		default state S0 {}\n"
        		+ "		state S1 {\n"
        		+ "			conc state R2 [IE2] {\n"
        		+ "				default state S0 {}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		trans T0 {\n"
        		+ "			from S0\n"
        		+ "			goto S1\n"
        		+ "		}\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        if (alloyModule.getConfLevels().size() != 3) {
        	throw new Exception("Configurations are not stored properly.");
        }
        
        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }

        List<String> rels = new ArrayList<String>();
        for (Decl f : snapshot.getFieldDecls()) {
        	rels.add(f.get().toString());
        }
        
        if (!rels.contains("field (this/Snapshot <: conf1)")) {
        	throw new Exception("conf1 is missing from the Snapshot relation.");
        }
        if (!rels.contains("field (this/Snapshot <: conf2)")) {
        	throw new Exception("conf2 is missing from the Snapshot relation.");
        }
        if (!rels.contains("field (this/Snapshot <: conf3)")) {
        	throw new Exception("conf3 is missing from the Snapshot relation.");
        }

        DashValidation.clearContainers();
    }
    
    // Check if conf1 maps to Identifier -> Statelabel, conf2 to Identifier -> Identifier -> StateLabel and so on.
    @Test
    public void testNestedConfRelExpressions() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "	conc state C {\n"
        		+ "		default state S0 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state R1 [IE1] {\n"
        		+ "		default state S0 {}\n"
        		+ "		state S1 {\n"
        		+ "			conc state R2 [IE2] {\n"
        		+ "				default state S0 {}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		trans T0 {\n"
        		+ "			from S0\n"
        		+ "			goto S1\n"
        		+ "		}\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        if (alloyModule.getConfLevels().size() != 3) {
        	throw new Exception("Configurations are not stored properly.");
        }
        
        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }

        for (Decl f : snapshot.getFieldDecls()) {
        	if(f.get().toString().contains("field (this/Snapshot <: conf1)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/StateLabel")) {
        			throw new Exception("conf1 mapping not stored properly");
        		}
        	}
        	if(f.get().toString().contains("field (this/Snapshot <: conf2)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/StateLabel")) {
        			throw new Exception("conf2 mapping not stored properly");
        		}
        	}
        	if(f.get().toString().contains("field (this/Snapshot <: conf3)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/StateLabel")) {
        			throw new Exception("conf3 mapping not stored properly");
        		}
        	}
        }
        
        DashValidation.clearContainers();
    }
    
    // Check if we have the taken1, taken2 and taken3 relations
    @Test
    public void testNestedTakenRelNames() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "	conc state C {\n"
        		+ "		default state S0 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state R1 [IE1] {\n"
        		+ "		default state S0 {}\n"
        		+ "		state S1 {\n"
        		+ "			conc state R2 [IE2] {\n"
        		+ "				default state S0 {}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		trans T0 {\n"
        		+ "			from S0\n"
        		+ "			goto S1\n"
        		+ "		}\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }

        List<String> rels = new ArrayList<String>();
        for (Decl f : snapshot.getFieldDecls()) {
        	rels.add(f.get().toString());
        }
        
        if (!rels.contains("field (this/Snapshot <: taken1)")) {
        	throw new Exception("conf1 is missing from the Snapshot relation.");
        }
        if (!rels.contains("field (this/Snapshot <: taken2)")) {
        	throw new Exception("conf2 is missing from the Snapshot relation.");
        }
        if (!rels.contains("field (this/Snapshot <: taken3)")) {
        	throw new Exception("conf3 is missing from the Snapshot relation.");
        }

        DashValidation.clearContainers();
    }
    
    // Check if conf1 maps to Identifier -> TransitionLabel, conf2 to Identifier -> Identifier -> TransitionLabel and so on.
    @Test
    public void testNestedTakenRelExpressions() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "	conc state C {\n"
        		+ "		default state S0 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state R1 [IE1] {\n"
        		+ "		default state S0 {}\n"
        		+ "		state S1 {\n"
        		+ "			conc state R2 [IE2] {\n"
        		+ "				default state S0 {}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		trans T0 {\n"
        		+ "			from S0\n"
        		+ "			goto S1\n"
        		+ "		}\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }

        for (Decl f : snapshot.getFieldDecls()) {
        	if(f.get().toString().contains("field (this/Snapshot <: taken1)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/TransitionLabel")) {
        			throw new Exception("taken1 mapping not stored properly");
        		}
        	}
        	if(f.get().toString().contains("field (this/Snapshot <: taken2)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/TransitionLabel")) {
        			throw new Exception("taken2 mapping not stored properly");
        		}
        	}
        	if(f.get().toString().contains("field (this/Snapshot <: taken3)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/TransitionLabel")) {
        			throw new Exception("taken3 mapping not stored properly");
        		}
        	}
        }
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testPostCondConfInNestedState () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        conc state C {\n"
        		+ "        	default state S0 {}\n"
        		+ "        }\n"
        		+ "						\n"
        		+ "        conc state R1 [IE1] {\n"
        		+ "        	default state S0 {}\n"
        		+ "        	state S1 {\n"
        		+ "        		conc state R2 [IE2] {\n"
        		+ "        			default state S0 {}\n"
        		+ "					state S1 {}\n"
        		+ "					trans T1 {\n"
        		+ "						from S0\n"
        		+ "						goto S1\n"
        		+ "				}\n"
        		+ "        		}\n"
        		+ "        	}\n"
        		+ "        	trans T0 {\n"
        		+ "        		from S0\n"
        		+ "        		goto S1\n"
        		+ "        	}\n"
        		+ "        }\n"
        		+ "}\n";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Expr f = alloyModule.funcs.get("pos_R0_R1_S1_R2_T1").get(0).getBody();
        
        String expectedConf = "s_next . (this/Snapshot <: conf1) = s . (this/Snapshot <: conf1), s_next . (this/Snapshot <: conf2) = s . (this/Snapshot <: conf2), s_next . (this/Snapshot <: conf3) = s . (this/Snapshot <: conf3) - p0 -> p1 -> p2 -> this/R0_R1_S1_R2_S0 + p0 -> p1 -> p2 -> this/R0_R1_S1_R2_S1,";
        if (!f.toString().contains(expectedConf)) {
        	throw new Exception("The conf relation is not updated properly in the post condition.");
        }
        
        //this/R0_R1_S1_R2_S0 in p2 . p1 . p0 . s . (this/Snapshot <: conf3)
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testPreCondConfInNestedState () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        conc state C {\n"
        		+ "        	default state S0 {}\n"
        		+ "        }\n"
        		+ "						\n"
        		+ "        conc state R1 [IE1] {\n"
        		+ "        	default state S0 {}\n"
        		+ "        	state S1 {\n"
        		+ "        		conc state R2 [IE2] {\n"
        		+ "        			default state S0 {}\n"
        		+ "					state S1 {}\n"
        		+ "					trans T1 {\n"
        		+ "						from S0\n"
        		+ "						goto S1\n"
        		+ "				}\n"
        		+ "        		}\n"
        		+ "        	}\n"
        		+ "        	trans T0 {\n"
        		+ "        		from S0\n"
        		+ "        		goto S1\n"
        		+ "        	}\n"
        		+ "        }\n"
        		+ "}\n";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Expr f = alloyModule.funcs.get("pre_R0_R1_S1_R2_T1").get(0).getBody();
        
        String expectedConf = "this/R0_R1_S1_R2_S0 in p2 . p1 . p0 . s . (this/Snapshot <: conf3)";
        if (!f.toString().contains(expectedConf)) {
        	throw new Exception("The conf relation is not updated properly in the pre condition.");
        }
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testSemanticsInNestedState () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        conc state C {\n"
        		+ "        	default state S0 {}\n"
        		+ "        }\n"
        		+ "						\n"
        		+ "        conc state R1 [IE1] {\n"
        		+ "        	default state S0 {}\n"
        		+ "        	state S1 {\n"
        		+ "        		conc state R2 [IE2] {\n"
        		+ "        			default state S0 {}\n"
        		+ "					state S1 {}\n"
        		+ "					trans T1 {\n"
        		+ "						from S0\n"
        		+ "						goto S1\n"
        		+ "				}\n"
        		+ "        		}\n"
        		+ "        	}\n"
        		+ "        	trans T0 {\n"
        		+ "        		from S0\n"
        		+ "        		goto S1\n"
        		+ "        	}\n"
        		+ "        }\n"
        		+ "}\n";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Expr f = alloyModule.funcs.get("semantics_R0_R1_S1_R2_T1").get(0).getBody();
        
        String expectedSemantics = "(s . (this/Snapshot <: stable) = boolean/True => AND[s_next . (this/Snapshot <: taken3) = p0 -> p1 -> p2 -> this/R0_R1_S1_R2_T1, no s_next . (this/Snapshot <: taken1), no s_next . (this/Snapshot <: taken2)] else AND[s_next . (this/Snapshot <: taken3) = s . (this/Snapshot <: taken3) + p0 -> p1 -> p2 -> this/R0_R1_S1_R2_T1, s_next . (this/Snapshot <: taken1) = s . (this/Snapshot <: taken1), s_next . (this/Snapshot <: taken2) = s . (this/Snapshot <: taken2), no p2 . p1 . p0 . s . (this/Snapshot <: taken3)])";
        if (!f.toString().contains(expectedSemantics)) {
        	throw new Exception("The conf relation is not updated properly in the pre condition." + f);
        }
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testNestedEvent () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        		conc state C {\n"
        		+ "        			default state S0 {}\n"
        		+ "        		}\n"
        		+ "\n"
        		+ "       	 	conc state R1 [IE1] {\n"
        		+ "		   			event E0 {}\n"
        		+ "        			default state S0 {}\n"
        		+ "        			state S1 {\n"
        		+ "        				conc state R2 [IE2] {\n"
        		+ "							event E1 {}\n"
        		+ "        					default state S0 {}\n"
        		+ "							state S1 {}\n"
        		+ "							trans T1 {\n"
        		+ "								on E1\n"
        		+ "								from S0\n"
        		+ "								goto S1\n"
        		+ "								send E1\n"
        		+ "							}\n"	
        		+ "        				}\n"
        		+ "        			}\n"
        		+ "        			trans T0 {\n"
        		+ "					on E0\n"
        		+ "        				from S0\n"
        		+ "        				goto S1\n"
        		+ "						send E0\n"
        		+ "        			}\n"
        		+ "        		}\n"
        		+ "			}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        if (alloyModule.events.size() != 2) {
        	throw new Exception("Nested Events not stored properly");
        }
        
        if (!alloyModule.events.keySet().contains("R0_R1_S1_R2_E1")) {
        	throw new Exception("Nested Events not stored properly");
        }
        
        if (!alloyModule.events.keySet().contains("R0_R1_E0")) {
        	throw new Exception("Nested Events not stored properly");
        }
        
        DashValidation.clearContainers();
    }
    
    // Check if we have the event1, event2 and event3 relations
    @Test
    public void testNestedEventRelNames() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        		conc state C {\n"
        		+ "        			default state S0 {}\n"
        		+ "        		}\n"
        		+ "\n"
        		+ "       	 	conc state R1 [IE1] {\n"
        		+ "		   			event E0 {}\n"
        		+ "        			default state S0 {}\n"
        		+ "        			state S1 {\n"
        		+ "        				conc state R2 [IE2] {\n"
        		+ "							event E1 {}\n"
        		+ "        					default state S0 {}\n"
        		+ "							state S1 {}\n"
        		+ "							trans T1 {\n"
        		+ "								on E1\n"
        		+ "								from S0\n"
        		+ "								goto S1\n"
        		+ "								send E1\n"
        		+ "							}\n"	
        		+ "        				}\n"
        		+ "        			}\n"
        		+ "        			trans T0 {\n"
        		+ "					on E0\n"
        		+ "        				from S0\n"
        		+ "        				goto S1\n"
        		+ "						send E0\n"
        		+ "        			}\n"
        		+ "        		}\n"
        		+ "			}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);    

        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }
        
        List<String> rels = new ArrayList<String>();
        for (Decl f : snapshot.getFieldDecls()) {
        	rels.add(f.get().toString());
        }
        
        if (!rels.contains("field (this/Snapshot <: events2)")) {
        	throw new Exception("event2 is missing from the Snapshot relation.");
        }
        if (!rels.contains("field (this/Snapshot <: events3)")) {
        	throw new Exception("event3 is missing from the Snapshot relation.");
        }

        DashValidation.clearContainers();
    }
    
    // Check if event1 maps to Identifier -> EventLabel, event2 to Identifier -> Identifier -> EventLabel and so on.
    @Test
    public void testNestedEventRelExpressions() throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        		conc state C {\n"
        		+ "        			default state S0 {}\n"
        		+ "        		}\n"
        		+ "\n"
        		+ "       	 	conc state R1 [IE1] {\n"
        		+ "		   			event E0 {}\n"
        		+ "        			default state S0 {}\n"
        		+ "        			state S1 {\n"
        		+ "        				conc state R2 [IE2] {\n"
        		+ "							event E1 {}\n"
        		+ "        					default state S0 {}\n"
        		+ "							state S1 {}\n"
        		+ "							trans T1 {\n"
        		+ "								on E1\n"
        		+ "								from S0\n"
        		+ "								goto S1\n"
        		+ "								send E1\n"
        		+ "							}\n"	
        		+ "        				}\n"
        		+ "        			}\n"
        		+ "        			trans T0 {\n"
        		+ "					on E0\n"
        		+ "        				from S0\n"
        		+ "        				goto S1\n"
        		+ "						send E0\n"
        		+ "        			}\n"
        		+ "        		}\n"
        		+ "			}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");;
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);

        Sig snapshot = null;
        for (Sig sig : alloyModule.getAllSigs()) {
            if (sig.label.equals("this/Snapshot")) {
                snapshot = sig;
            }
        }

        for (Decl f : snapshot.getFieldDecls()) {
        	if(f.get().toString().contains("field (this/Snapshot <: events2)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/EventLabel")) {
        			throw new Exception("conf2 mapping not stored properly");
        		}
        	}
        	if(f.get().toString().contains("field (this/Snapshot <: events3)")) {
        		if(!f.expr.toString().equals("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/EventLabel")) {
        			throw new Exception("conf3 mapping not stored properly");
        		}
        	}
        }
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testEventPreCondExpr () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        		conc state C {\n"
        		+ "        			default state S0 {}\n"
        		+ "        		}\n"
        		+ "\n"
        		+ "       	 	conc state R1 [IE1] {\n"
        		+ "		   			event E0 {}\n"
        		+ "        			default state S0 {}\n"
        		+ "        			state S1 {\n"
        		+ "        				conc state R2 [IE2] {\n"
        		+ "							event E1 {}\n"
        		+ "        					default state S0 {}\n"
        		+ "							state S1 {}\n"
        		+ "							trans T1 {\n"
        		+ "								on E1\n"
        		+ "								from S0\n"
        		+ "								goto S1\n"
        		+ "								send E1\n"
        		+ "							}\n"	
        		+ "        				}\n"
        		+ "        			}\n"
        		+ "        			trans T0 {\n"
        		+ "					on E0\n"
        		+ "        				from S0\n"
        		+ "        				goto S1\n"
        		+ "						send E0\n"
        		+ "        			}\n"
        		+ "        		}\n"
        		+ "			}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Expr f = alloyModule.funcs.get("pre_R0_R1_S1_R2_T1").get(0).getBody();
        
        String expectedConf = "this/R0_R1_S1_R2_E1 in p2 . p1 . p0 . s . (this/Snapshot <: events3)";
        if (!f.toString().contains(expectedConf)) {
        	throw new Exception("The event relation is not checked properly in the pre condition." + f);
        }
        
        DashValidation.clearContainers();
    }
    
    @Test
    public void testTestIfnNextStableCallPostCondExpr () throws Exception {
        String dashModel = "conc state R0 [IE0] {\n"
        		+ "        		conc state C {\n"
        		+ "        			default state S0 {}\n"
        		+ "        		}\n"
        		+ "\n"
        		+ "       	 	conc state R1 [IE1] {\n"
        		+ "		   			event E0 {}\n"
        		+ "        			default state S0 {}\n"
        		+ "        			state S1 {\n"
        		+ "        				conc state R2 [IE2] {\n"
        		+ "							event E1 {}\n"
        		+ "        					default state S0 {}\n"
        		+ "							state S1 {}\n"
        		+ "							trans T1 {\n"
        		+ "								on E1\n"
        		+ "								from S0\n"
        		+ "								goto S1\n"
        		+ "								send E1\n"
        		+ "							}\n"	
        		+ "        				}\n"
        		+ "        			}\n"
        		+ "        			trans T0 {\n"
        		+ "					on E0\n"
        		+ "        				from S0\n"
        		+ "        				goto S1\n"
        		+ "						send E0\n"
        		+ "        			}\n"
        		+ "        		}\n"
        		+ "			}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashModule alloyModule = new CoreDashToAlloy().convertToAlloyAST(coreDashModule, "", "");
        A4Reporter rep = new A4Reporter();
        alloyModule = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloyModule);
        
        Expr f = alloyModule.funcs.get("pos_R0_R1_S1_R2_T1").get(0).getBody();
        
        String expectedCall = "(this/testIfNextStable3[s, s_next, this/R0_R1_S1_R2_T1, p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1] => "
        		+ "AND[s_next . (this/Snapshot <: stable) = boolean/True, (s . (this/Snapshot <: stable) = boolean/True => "
        		+ "AND[s_next . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/InternalEvent = none -> none -> none, s_next . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/InternalEvent = p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1] else "
        		+ "AND[s_next . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/InternalEvent = none -> none -> none + s . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/InternalEvent, s_next . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/InternalEvent = p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1 + s . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/InternalEvent])] else "
        		+ "AND[s_next . (this/Snapshot <: stable) = boolean/False, (s . (this/Snapshot <: stable) = boolean/True => "
        		+ "AND[s_next . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/InternalEvent = none -> none -> none, s_next . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/EnvironmentEvent = s . (this/Snapshot <: events2) & this/Identifiers -> this/Identifiers -> this/EnvironmentEvent, s_next . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/InternalEvent = p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1, s_next . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/EnvironmentEvent = s . (this/Snapshot <: events3) & this/Identifiers -> this/Identifiers -> this/Identifiers -> this/EnvironmentEvent] else AND[s_next . (this/Snapshot <: events2) = s . (this/Snapshot <: events2) + none -> none -> none, s_next . (this/Snapshot <: events3) = s . (this/Snapshot <: events3) + p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1])]), p0 -> p1 -> p2 -> this/R0_R1_S1_R2_E1 in s_next . (this/Snapshot <: events3";
        if (!f.toString().contains(expectedCall)) {
        	throw new Exception("The event post condition is not handled correctly." + f);
        }
        
        DashValidation.clearContainers();
    }
}
