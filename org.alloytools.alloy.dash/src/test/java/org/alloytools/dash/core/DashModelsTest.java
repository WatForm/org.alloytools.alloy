package org.alloytools.dash.core;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;

import org.junit.Test;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import ca.uwaterloo.watform.ast.DashState;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.parser.DashHelper;
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
    }

    @Test
    public void testConcStates() throws Exception {

        String dashModel = "conc state topConcStateA { conc state innerConcState{  default state A {} } } conc state topConcStateB { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
  
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateA").getRawName(), "topConcStateA");
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateA").getInnerConcStates().get(0).getRawName(), "innerConcState");
        assertEquals(coreDashModule.getORStates().get("topConcStateA_innerConcState_A").getRawName(), "A");
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateB").getRawName(), "topConcStateB");
    }
     
    @Test
    public void testParamConcStates() throws Exception { 

        String dashModel = "conc state topConcStateA [PID1] { default state A {} } conc state topConcStateB [PID2] { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateA").getRawName(), "topConcStateA");
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateB").getRawName(), "topConcStateB");
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateA").getReplicatedIdentifier(), "PID1");
        assertEquals(coreDashModule.getAllConcurrentStates().get("topConcStateB").getReplicatedIdentifier(), "PID2");
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

        assertTrue(funcs0.get(0).getBody().toString().contains(expectedOutput1));
        assertTrue(funcs1.get(0).getBody().toString().contains(expectedOutput2));
    }
    
   
    @Test
    public void testTransitions() throws Exception {

        String dashModel = "conc state topConcStateA { event A{} trans A {on A goto B} default state B {trans B {on A}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
  
        assertEquals(coreDashModule.getTransitions().get("topConcStateA_A").getRawName(), "A");
        assertEquals(coreDashModule.getTransitions().get("topConcStateA_B_B").getRawName(), "B");
        assertEquals(coreDashModule.getTransitions().get("topConcStateA_A").getDestination().getAllDestinations().get(0), "topConcStateA_B");
        assertEquals(coreDashModule.getTransitions().get("topConcStateA_B_B").getTriggerEvent().getRawName(), "topConcStateA_A");
    }

    @Test
    public void testVarNames() throws Exception {

        String dashModel = "conc state concState { var_one: none->none var_two: none->none conc state innerConcState {var_three: none->none} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashOptions.isElectrum = false;

        assertEquals(module.getRawVarNames().get("concState").get(0), "var_one");
        assertEquals(module.getRawVarNames().get("concState").get(1), "var_two");
        assertEquals(module.getRawVarNames().get("concState_innerConcState").get(0), "var_three");
    }
    
    @Test
    public void testORStateVarNames() throws Exception {

        String dashModel = "conc state concState { "
        		+ "default state innerORState0 {var_one: none->none} "
        		+ "state innerORState1 {"
        		+ "	var_one: none->none "
        		+ "	var_two: none->none"
        		+ "	state innerORState2 {"
        		+ "	var_one: none->none"
        		+ "	}"
        		+ "}"
        		+ "}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashOptions.isElectrum = false;

        assertEquals(module.getRawVarNames().get("concState_innerORState0").get(0), "var_one");
        assertEquals(module.getRawVarNames().get("concState_innerORState1").get(0), "var_one");
        assertEquals(module.getRawVarNames().get("concState_innerORState1").get(1), "var_two");
        assertEquals(module.getRawVarNames().get("concState_innerORState1_innerORState2").get(0), "var_one");
    }
    
    @Test
    public void testEventNames() throws Exception {

        String dashModel = "conc state concState { "
        		+ "default state innerORState0 {event e0 {}} "
        		+ "state innerORState1 {"
        		+ "	event e0 {}"
        		+ "	event e1 {}"
        		+ "	state innerORState2 {"
        		+ "	event e0 {}"
        		+ "	}"
        		+ "}"
        		+ "}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashOptions.isElectrum = false;

        Optional<DashState> innerORState0 = module.getAllConcurrentStates().get("concState").getInnerORStates().stream().filter(x -> x.getRawName().equals("innerORState0")).findFirst();
        Optional<DashState> innerORState1 = module.getAllConcurrentStates().get("concState").getInnerORStates().stream().filter(x -> x.getRawName().equals("innerORState1")).findFirst();
        Optional<DashState> innerORState2 = innerORState1.get().getInnerORStates().stream().filter(x -> x.getRawName().equals("innerORState2")).findFirst();
        assertEquals("e0", innerORState0.get().getEventNames().get(0));
        assertEquals("e0", innerORState1.get().getEventNames().get(0));
        assertEquals("e1", innerORState1.get().getEventNames().get(1));
        assertEquals("e0", innerORState2.get().getEventNames().get(0));
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
        for (DashTrans trans : coreDashModule.getTransitions().values())
            transitions.add(trans);

        assertEquals(transitions.size(), 3);
        assertEquals(transitions.get(0).getFullyQualName(), "concState_t_1");
        assertEquals(transitions.get(1).getFullyQualName(), "concState_trans_two");
        assertEquals(transitions.get(2).getFullyQualName(), "concState_state_one_t_2");
    }

    @Test
    public void testTransitionIncompleteCommand() throws Exception {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.getTransitions().values()) {
            transitions.add(trans);
        }
        
        assertEquals(transitions.size(), 3);
        
        assertEquals(transitions.get(0).getOrigin().getAllOrigins().get(0), "concState");
        assertEquals(transitions.get(0).getDestination().getAllDestinations().get(0), "concState");
        
        assertEquals(transitions.get(1).getOrigin().getAllOrigins().get(0), "concState");
        assertEquals(transitions.get(1).getOrigin().getAllOrigins().get(0), "concState");
        
        assertEquals(transitions.get(2).getOrigin().getAllOrigins().get(0), "concState/state_one");
        assertEquals(transitions.get(2).getOrigin().getAllOrigins().get(0), "concState/state_one");

    }

    @Test
    public void testTransitionAllCommands() throws Exception {

        String dashModel = 
        		"conc state concState { "
	        		+ "var_one: none event "
	        		+ "event_one {} "
	        		+ "default state state_one {} "
	        		+ "state state_two {} "
	        		+ "trans {"
	        			+ "from state_one, state_two "
	        			+ "on event_one "
	        			+ "when var_one = none "
	        			+ "do var_one' = var_one "
	        			+ "goto state_two "
	        			+ "send event_one "
	        		+ "}"
        		+ "}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.getTransitions().values()) {
            transitions.add(trans);
        }

        assertEquals(transitions.get(0).getOrigin().getAllOrigins().get(0), "concState_state_one");
        assertEquals(transitions.get(0).getTriggerEvent().getRawName(), "concState_event_one");
        assertEquals(transitions.get(0).getAction().getAllExpression().get(0).toString(), "var_one' = var_one");
        assertEquals(transitions.get(0).getCondition().getAllExpressions().get(0).toString(), "var_one = none");
        assertEquals(transitions.get(0).getDestination().getAllDestinations().get(0), "concState_state_two");
        assertEquals(transitions.get(0).getEventsTriggered().getRawName(), "concState_event_one");

        assertEquals(transitions.get(1).getOrigin().getAllOrigins().get(0), "concState_state_two");
        assertEquals(transitions.get(1).getTriggerEvent().getRawName(), "concState_event_one");
        assertEquals(transitions.get(1).getAction().getAllExpression().get(0).toString(), "var_one' = var_one");
        assertEquals(transitions.get(1).getCondition().getAllExpressions().get(0).toString(), "var_one = none");
        assertEquals(transitions.get(1).getDestination().getAllDestinations().get(0), "concState_state_two");
        assertEquals(transitions.get(1).getEventsTriggered().getRawName(), "concState_event_one");
    }

    @Test
    public void testTransitionTemplate() throws Exception {

        String dashModel = "conc state concState { var_one: none event event_one {} def trans template [s: State, e: Event] {from s, state_two on e when var_one = none do var_one' = var_one goto s send e} default state state_one {} state state_two {} trans{ template[state_one, event_one]} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : coreDashModule.getTransitions().values()) {
            transitions.add(trans);
        }
        
        assertEquals(transitions.get(0).getOrigin().getAllOrigins().get(0), "concState_state_one");
        assertEquals(transitions.get(0).getTriggerEvent().getRawName(), "concState_event_one");
        assertEquals(transitions.get(0).getAction().getAllExpression().get(0).toString(), "var_one' = var_one");
        assertEquals(transitions.get(0).getCondition().getAllExpressions().get(0).toString(), "var_one = none");
        assertEquals(transitions.get(0).getDestination().getAllDestinations().get(0), "concState_state_one");
        assertEquals(transitions.get(0).getEventsTriggered().getRawName(), "concState_event_one");

        assertEquals(transitions.get(1).getOrigin().getAllOrigins().get(0), "concState_state_two");
        assertEquals(transitions.get(1).getTriggerEvent().getRawName(), "concState_event_one");
        assertEquals(transitions.get(1).getAction().getAllExpression().get(0).toString(), "var_one' = var_one");
        assertEquals(transitions.get(1).getCondition().getAllExpressions().get(0).toString(), "var_one = none");
        assertEquals(transitions.get(1).getDestination().getAllDestinations().get(0), "concState_state_one");
        assertEquals(transitions.get(1).getEventsTriggered().getRawName(), "concState_event_one");
    }
    
    @Test
    public void testTransitionToNestedDefaultState() throws Exception {

        String dashModel = "conc state ANDState {\n"
        		+ "	state ORState {\n"
        		+ "		default state NestedDefaultState {}	\n"
        		+ "	}\n"
        		+ "	default state Default {}\n"
        		+ "	trans transition {\n"
        		+ "		goto ORState\n"
        		+ "	}\n"
        		+ "}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        assertTrue(coreDashModule.getInitDefaultStates().values().stream().anyMatch(x -> x.get(0).getFullyQualName().equals("ANDState_Default")));
        assertTrue(coreDashModule.getTransitions().get("ANDState_transition").getDestination().getAllDestinations().get(0).equals("ANDState_ORState_NestedDefaultState"));
    }
    
    @Test
    public void testTransitionToFromNestedANDState() throws Exception {

        String dashModel = "conc state ANDState {\n"
        		+ "	default state Default {\n"
        		+ "		conc state InnerANDOne {\n"
        		+ "			default state InnerDefaultOne {}\n"
        		+ "		}\n"
        		+ "		conc state InnerANDTwo {\n"
        		+ "			default state InnerDefaultTwo {}\n"
        		+ "			trans InnerTransTwo {\n"
        		+ "				from InnerDefaultTwo\n"
        		+ "				goto External\n"
        		+ "			}\n"
        		+ "		}	\n"
        		+ "	}\n"
        		+ "	state External {}\n"
        		+ "	trans transition {\n"
        		+ "		from External\n"
        		+ "		goto Default\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashOptions.isElectrum = false;
        
        assertEquals(coreDashModule.getInitDefaultStates().get(0).get(0).getFullyQualName(), "ANDState_Default_InnerANDOne_InnerDefaultOne");
        assertEquals(coreDashModule.getInitDefaultStates().get(0).get(1).getFullyQualName(), "ANDState_Default_InnerANDTwo_InnerDefaultTwo");

        assertEquals(coreDashModule.getTransitions().get("ANDState_transition").getDestination().getAllDestinations().get(0), "ANDState_Default");
        assertEquals(coreDashModule.getTransitions().get("ANDState_transition").getOrigin().getAllOrigins().get(0), "ANDState_External");
        
        assertTrue(coreDashModule.getTransitions().containsKey("ANDState_Default_InnerANDTwo_InnerTransTwo"));
        assertTrue(coreDashModule.getTransitions().get("ANDState_Default_InnerANDTwo_InnerTransTwo").getOrigin().isTransitionToParentState());
        
        assertEquals(coreDashModule.getTransitions().get("ANDState_Default_InnerANDTwo_InnerTransTwo").getDestination().getAllDestinations().get(0), "ANDState_External");
        assertEquals(new LinkedHashMap<Integer, Expr>(DashHelper.calculateConf2FromExpr(coreDashModule.getTransitions().get("ANDState_Default_InnerANDTwo_InnerTransTwo"))).get(0).toString(),
        		"ANDState_Default");
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
        
        assertTrue(coreDashModule.funcs.keySet().contains("pre_topConcStateA_A"));
        assertTrue(coreDashModule.funcs.keySet().contains("pos_topConcStateA_A"));
        assertTrue(coreDashModule.funcs.keySet().contains("topConcStateA_A"));
        assertTrue(coreDashModule.funcs.keySet().contains("semantics_topConcStateA_A"));

        assertTrue(coreDashModule.funcs.keySet().contains("pre_topConcStateA_B_B"));
        assertTrue(coreDashModule.funcs.keySet().contains("pos_topConcStateA_B_B"));
        assertTrue(coreDashModule.funcs.keySet().contains("topConcStateA_B_B"));
        assertTrue(coreDashModule.funcs.keySet().contains("semantics_topConcStateA_B_B"));
        
        assertTrue(coreDashModule.funcs.keySet().contains("init"));
        assertTrue(coreDashModule.funcs.keySet().contains("small_step"));
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

        assertTrue(coreDashModule.sigs.keySet().contains("Snapshot"));
        assertTrue(coreDashModule.sigs.keySet().contains("SystemState"));
        assertTrue(coreDashModule.sigs.keySet().contains("topConcStateA"));
        assertTrue(coreDashModule.sigs.keySet().contains("topConcStateA_B"));
        assertTrue(coreDashModule.sigs.keySet().contains("topConcStateA_envA"));
        assertTrue(coreDashModule.sigs.keySet().contains("topConcStateA_A"));
        assertTrue(coreDashModule.sigs.keySet().contains("topConcStateA_B_B"));
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs0.get(0).getBody().toString(), expectedOutput1);
        assertEquals(funcs1.get(0).getBody().toString(), expectedOutput2);
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

        assertEquals(funcs0.get(0).getBody().toString(), expectedOutput1);
        assertEquals(funcs1.get(0).getBody().toString(), expectedOutput2);
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
              
        List<String> buffers = new ArrayList<String>();
        List<String> bufferElems = new ArrayList<String>();
        DashOptions.isElectrum = false;
        
        for (String name : module.getBufferElement().keySet()) {
        	buffers.add(name);
        	bufferElems.add(module.getBufferElement().get(name));
        }

        assertEquals(buffers.get(0), "Parent_Child1_buf1");
        assertEquals(buffers.get(1).toString(), "Parent_Child2_buf2");
        assertEquals(bufferElems.get(0), "PID1");
        assertEquals(bufferElems.get(1).toString(), "PID2");
    } 
    
    
    @Test
    public void testEnabledAfterNextStep() throws Exception {
        String dashModel = "conc state concState { "
        		+ "var_one: one EventLabel "
        		+ "event envA {} "
        		+ "conc state inner { "
	        		+ "		default state stateA{} "
	        		+ "		trans A {"
	        		+ "			from stateA "
	        		+ "			on envA when var_one = none"
	        		+ "		}"
	        		+ "		trans B {"
	        		+ "			from stateA "
	        		+ "			on envA "
	        		+ "			do var_one' = none"
	        		+ "		} "
	        		+ "} "
        		+ "}";
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
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

        assertEquals(funcs.get(0).getBody().toString(), expectedOutput);
    }
    
    @Test
    public void testNestedDefaultState() throws Exception {
        String dashModel = "conc state ANDState {"
        		+ "	default state ORState {"
        		+ "		trans A {"
        		+ "			goto Dummy"
        		+ "		}"
        		+ "		default state Default {}"
        		+ "		state Dummy {}"
        		+ "	}"
        		+ "	state Dummy {}"
        		+ "}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashModule coreDashModule = new DashToCoreDash().transformToCoreDash(module, "", "");
        DashValidation.validateDashModel(module);
        new CoreDashToAlloy().convertToAlloyAST(module, "", "");
        DashOptions.isElectrum = false;

        assertTrue(coreDashModule.getInitDefaultStates().values().stream().anyMatch(x -> x.get(0).getFullyQualName().equals("ANDState_ORState_Default")));
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

        assertEquals(coreDashModule.facts.get(0).b.toString(), expectedOutput);
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

        assertEquals(coreDashModule.facts.get(2).b.toString(), expectedOutput);
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

        assertTrue(alloyModule.getConcurrentStateNames().contains("R0"));
        assertTrue(alloyModule.getConcurrentStateNames().contains("R0_R1"));
        assertTrue(alloyModule.getConcurrentStateNames().contains("R0_R1_S1_R2"));
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
        
        assertTrue(rels.contains("field (this/Snapshot <: conf1)"));
        assertTrue(rels.contains("field (this/Snapshot <: conf2)"));
        assertTrue(rels.contains("field (this/Snapshot <: conf3)"));
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
        
        assertTrue(snapshot.getFieldDecls().get(0).get().toString().contains("field (this/Snapshot <: conf1)"));
        assertTrue(snapshot.getFieldDecls().get(1).get().toString().contains("field (this/Snapshot <: conf2)"));
        assertTrue(snapshot.getFieldDecls().get(2).get().toString().contains("field (this/Snapshot <: conf3)"));
        
        assertEquals(snapshot.getFieldDecls().get(0).expr.toString(), ("this/Identifiers -> this/StateLabel"));
        assertEquals(snapshot.getFieldDecls().get(1).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/StateLabel"));
        assertEquals(snapshot.getFieldDecls().get(2).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/StateLabel"));
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
        
        assertTrue(rels.contains("field (this/Snapshot <: taken1)"));
        assertTrue(rels.contains("field (this/Snapshot <: taken2)"));
        assertTrue(rels.contains("field (this/Snapshot <: taken3)"));
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
        
        assertTrue(snapshot.getFieldDecls().get(3).get().toString().contains("field (this/Snapshot <: taken1)"));
        assertTrue(snapshot.getFieldDecls().get(4).get().toString().contains("field (this/Snapshot <: taken2)"));
        assertTrue(snapshot.getFieldDecls().get(5).get().toString().contains("field (this/Snapshot <: taken3)"));
        
        assertEquals(snapshot.getFieldDecls().get(3).expr.toString(), ("this/Identifiers -> this/TransitionLabel"));
        assertEquals(snapshot.getFieldDecls().get(4).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/TransitionLabel"));
        assertEquals(snapshot.getFieldDecls().get(5).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/TransitionLabel"));
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
        
        assertTrue(f.toString().contains(expectedConf));
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
        assertTrue(f.toString().contains(expectedConf));
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
        assertTrue(f.toString().contains(expectedSemantics));
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
        
        assertEquals(alloyModule.getEvents().size(), 2);
        assertTrue(alloyModule.getEvents().keySet().contains("R0_R1_S1_R2_E1"));
        assertTrue(alloyModule.getEvents().keySet().contains("R0_R1_E0"));
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
        
        assertTrue(rels.contains("field (this/Snapshot <: events2)"));
        assertTrue(rels.contains("field (this/Snapshot <: events3)"));
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
        
        assertEquals(snapshot.getFieldDecls().get(6).get().toString(), ("field (this/Snapshot <: events2)"));
        assertEquals(snapshot.getFieldDecls().get(7).get().toString(), ("field (this/Snapshot <: events3)"));
        assertEquals(snapshot.getFieldDecls().get(6).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/EventLabel"));
        assertEquals(snapshot.getFieldDecls().get(7).expr.toString(), ("this/Identifiers -> this/Identifiers -> this/Identifiers -> this/EventLabel"));
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

        assertTrue(f.toString().contains(expectedConf));
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
        assertTrue(f.toString().contains(expectedCall));
    }
}
