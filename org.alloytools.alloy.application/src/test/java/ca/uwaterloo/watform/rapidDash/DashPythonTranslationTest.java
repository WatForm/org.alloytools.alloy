/**
 * Test the translation data structure.
 */

package ca.uwaterloo.watform.rapidDash;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.*;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;


public class DashPythonTranslationTest {
    private InputStream sysInBackup;

    private long findStateOccurncesInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getRootStates().stream().filter(state -> state.getName().equals(stateName)).count();
    }

    private DashPythonTranslation.State findStateInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getRootStates().stream().filter(state -> state.getName().equals(stateName)).findAny().get();
    }

    @Before
    public void initInput(){
        sysInBackup = System.in;
        String noConfig = "n" + System.lineSeparator();
        String userInput = new String(new char[30]).replace("\0", "3" + System.lineSeparator());
        System.setIn(new ByteArrayInputStream((noConfig + userInput).getBytes()));
    }

    @After
    public void closeInput(){
        System.setIn(sysInBackup);
    }
    @Test
    public void testStates() throws Exception {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);
        assertEquals(1, translation.getRootStates().size());
        assertEquals("concState", translation.getRootStates().get(0).getName());
        assertTrue("concState", translation.getRootStates().get(0).getIsConc());

        List<DashPythonTranslation.State> secondary_states = translation.getRootStates().get(0).getSubstates();

        assertEquals(2, secondary_states.size());
        HashMap<String, DashPythonTranslation.State> nameToState = new HashMap<>();
        for (DashPythonTranslation.State state : secondary_states)
        {
            nameToState.put(state.getName(), state);
        }
        assertTrue(nameToState.containsKey("concState_topStateB"));
        assertTrue(nameToState.containsKey("concState_topStateA"));

        List<DashPythonTranslation.State> tertiary_states = nameToState.get("concState_topStateA").getSubstates();

        assertEquals(1, tertiary_states.size());
        assertEquals("concState_topStateA_innerState", tertiary_states.get(0).getName());
    }

    @Test
    public void testStateInitAndUnnamedRelations() throws Exception {
        String dashModel = "sig Chair {} sig Player {} conc state Game { active_players: set Player active_chairs: set Chair occupied: Chair set -> set Player init { active_players = Player active_chairs = Chair occupied = none -> none}}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);
        assertEquals(1, translation.getRootStates().size());

        DashPythonTranslation.State gameState = translation.getRootStates().get(0);
        assertEquals(3, gameState.getDecls().size());
        assertEquals(3, gameState.getInits().size());

        for (String decl : gameState.getDecls()) {
            assertTrue(decl.contains("="));
        }

        System.out.println(gameState.getDecls());

        assertTrue(gameState.getDecls().contains("Game_active_players = Player('active_players', Multiplicity.Set)"));
        assertTrue(gameState.getDecls().contains("Game_active_chairs = Chair('active_chairs', Multiplicity.Set)"));
        assertTrue(gameState.getDecls().contains("Game_occupied = Chair * Player"));

        for (String init : gameState.getInits()) {
            assertTrue(init.contains("="));
        }
    }

    @Test
    public void testTransitions() throws Exception {
        String dashModel = "conc state topConcStateA { event A{} default state s1{} state s2{} trans t1 {from s2 on A goto s1} trans t2 {from s1 on A goto s2} }";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");

        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        DashPythonTranslation.State topState = translation.getRootStates().get(0);
        assertEquals("topConcStateA", topState.getName());

        DashPythonTranslation.State s1 =
                topState.getSubstates().stream().filter(state -> state.getName().equals("topConcStateA_s1")).findAny().get();
        assertEquals(1, s1.getTransitions().size());
        assertEquals("topConcStateA_s1", s1.getTransitions().get(0).getStateName());
        assertEquals("topConcStateA_s1", s1.getTransitions().get(0).getFromStateName());
        assertEquals("t2", s1.getTransitions().get(0).getTransName());

        DashPythonTranslation.State s2 =
                topState.getSubstates().stream().filter(state -> state.getName().equals("topConcStateA_s2")).findAny().get();
        assertEquals(1, s2.getTransitions().size());
        assertEquals("topConcStateA_s2", s2.getTransitions().get(0).getStateName());
        assertEquals("topConcStateA_s2", s2.getTransitions().get(0).getFromStateName());
        assertEquals("t1", s2.getTransitions().get(0).getTransName());
    }

    @Test
    public void testSignaturesMultiplicity() throws Exception {
        String dashModel = "sig Floor {}\n" +
                "one sig Chicken {}\n" +
                "some sig SomeSig {}\n" +
                "lone sig LoneSig {}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");

        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        assertEquals(4, translation.signatures.size());
        assertEquals(translation.signatures.get(0).name, "Floor");
        assertEquals(translation.signatures.get(0).multiplicity, "set");
        assertEquals(translation.signatures.get(0).scope, 3);
        assertEquals(translation.signatures.get(1).name, "Chicken");
        assertEquals(translation.signatures.get(1).multiplicity, "one");
        assertEquals(translation.signatures.get(1).scope, 1);
        assertEquals(translation.signatures.get(2).name, "SomeSig");
        assertEquals(translation.signatures.get(2).multiplicity, "some");
        assertEquals(translation.signatures.get(2).scope, 3);
        assertEquals(translation.signatures.get(3).name, "LoneSig");
        assertEquals(translation.signatures.get(3).multiplicity, "lone");
        assertEquals(translation.signatures.get(3).scope, 0);
    }

    @Test
    public void testSignaturesSubsetRelationships() throws Exception {
        String dashModel = "abstract sig A {}\n" +
                "sig B {}\n" +
                "sig C in A + B {}\n" +
                "sig D in C + A {}\n" +
                "sig AA extends A {}\n" +
                "sig AAA extends AA {}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");

        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        assertEquals(6, translation.signatures.size());
        assertEquals(translation.signatures.get(0).name, "A");
        assertEquals(translation.signatures.get(0).scope, 3);
        assertEquals(translation.signatures.get(1).name, "B");
        assertEquals(translation.signatures.get(1).isSubset, false);
        assertEquals(translation.signatures.get(1).parentNames.size(), 0);
        assertEquals(translation.signatures.get(2).name, "C");
        assertEquals(translation.signatures.get(2).isSubset, true);
        assertEquals(translation.signatures.get(2).parentNames, Arrays.asList("A", "B"));
        assertEquals(translation.signatures.get(3).name, "D");
        assertEquals(translation.signatures.get(3).isSubset, true);
        assertEquals(translation.signatures.get(3).parentNames, Arrays.asList("C", "A"));
        assertEquals(translation.signatures.get(4).name, "AA");
        assertEquals(translation.signatures.get(4).isSubsig, true);
        assertEquals(translation.signatures.get(4).parentName, "A");
        assertEquals(translation.signatures.get(5).name, "AAA");
        assertEquals(translation.signatures.get(5).isSubsig, true);
        assertEquals(translation.signatures.get(5).parentName, "AA");
    }

    @Test
    public void testSignatureAttributes() throws Exception {
        class Data{
            public String name;
            public int scope;
            public boolean isSubset;
            public boolean isSubsig;
            public boolean isAbstract;
            public String parentName;
            public String parentNames;
            public boolean hasChildSubsig;
            public Data(String name, int scope, boolean isSubset, boolean isSubsig, boolean isAbstract, boolean hasChildSubsig, String parentName, String parentNames){
                this.name = name;
                this.scope = scope;
                this.isSubset = isSubset;
                this.isSubsig = isSubsig;
                this.isAbstract = isAbstract;
                this.hasChildSubsig = hasChildSubsig;
                this.parentName = parentName;
                this.parentNames = parentNames;
            }
        }

        String dashModel =
            "sig A {}\n" +
            "sig A1 extends A {}\n" +
            "sig A2 extends A {}\n" +

            "abstract sig B {}\n" +
            "sig B1 extends B {}\n" +
            "sig B2 extends B {}\n" +

            "sig C1 {}\n" +
            "sig C2 {}\n" +
            "sig C3 {}\n" +
            "sig C in C1 + C2 + C3 {}\n" +


            "lone sig SLone_Lone {}\n" +
            "lone sig SLone_Lone_sub1 extends SLone_Lone {}\n" +
            "lone sig SLone_Lone_sub2 extends SLone_Lone {}\n" +


            "one sig SOne_One {}\n" +
            "lone sig SOne_Lone_sub1 extends SOne_One {}\n" +
            "lone sig SOne_Lone_sub2 extends SOne_One {}\n" +


            "lone sig SLone {}\n" +

            "lone sig SLone_Subsig_Lone extends SLone {}\n" +
            "one sig SLone_Subsig_One extends SLone {}\n" +
            "lone sig SLone_Subset_Lone in SLone {}\n" +
            "one sig SLone_Subset_One in SLone {}\n" +
            "some sig SLone_Subset_Some in SLone {}\n" +


            "one sig SOne {}\n" +

            "lone sig SOne_Subsig_Lone extends SOne {}\n" +
            "one sig SOne_Subsig_One extends SOne {}\n" +
            "lone sig SOne_Subset_Lone in SOne {}\n" +
            "one sig SOne_Subset_One in SOne {}\n" +
            "some sig SOne_Subset_Some in SOne {}\n" +


            "some sig SSome {}\n" +

            "lone sig SSome_Subsig_Lone extends SSome {}\n" +
            "one sig SSome_Subsig_One extends SSome {}\n" +
            "some sig SSome_Subsig_Some extends SSome {}\n" +
            "lone sig SSome_Subset_Lone in SSome {}\n" +
            "one sig SSome_Subset_One in SSome {}\n" +
            "some sig SSome_Subset_Some in SSome {}\n" +


            "abstract sig Object {}\n" +
            "one sig Chicken, Farmer, Fox extends Object {}\n";

        List<Data> expectedResults = Arrays.asList(
            new Data("A", 3, false, false, false, true,"", ""),
            new Data("A1", 3, false, true, false,false,"A", ""),
            new Data("A2", 3, false, true, false,false,"A", ""),

            new Data("B", 6, false, false, true, true,"", ""),
            new Data("B1", 3, false, true, false,false,"B", ""),
            new Data("B2", 3, false, true, false,false,"B", ""),

            new Data("C1", 3, false, false, false, false,"", ""),
            new Data("C2", 3, false, false, false, false,"", ""),
            new Data("C3", 3, false, false, false, false,"", ""),
            new Data("C", 3, true, false, false,false,"", "C1, C2, C3"),

            new Data("SLone_Lone", 0, false, false, false, true,"", ""),
            new Data("SLone_Lone_sub1", 0, false, true, false, false,"SLone_Lone", ""),
            new Data("SLone_Lone_sub2", 0, false, true, false, false,"SLone_Lone", ""),

            new Data("SOne_One", 1, false, false, false, true,"", ""),
            // TODO: currently no non-determinism is happening when picking the subsig to put the object
            new Data("SOne_Lone_sub1", 0, false, true, false, false,"SOne_One", ""),
            new Data("SOne_Lone_sub2", 0, false, true, false, false,"SOne_One", ""),


            new Data("SLone", 1, false, false, false, true,"", ""),
            new Data("SLone_Subsig_Lone", 0, false, true, false,false,"SLone", ""),
            new Data("SLone_Subsig_One", 1, false, true, false,false,"SLone", ""),

            new Data("SLone_Subset_Lone", 0, true, false, false,false,"", "SLone"),
            new Data("SLone_Subset_One", 1, true, false, false,false,"", "SLone"),
            new Data("SLone_Subset_Some", 1, true, false, false,false,"", "SLone"),


            new Data("SOne", 1, false, false, false, true,"", ""),
            new Data("SOne_Subsig_Lone", 0, false, true, false,false,"SOne", ""),
            new Data("SOne_Subsig_One", 1, false, true, false,false,"SOne", ""),

            new Data("SOne_Subset_Lone", 0, true, false, false,false,"", "SOne"),
            new Data("SOne_Subset_One", 1, true, false, false,false,"", "SOne"),
            new Data("SOne_Subset_Some", 1, true, false, false,false,"", "SOne"),


            new Data("SSome", 3, false, false, false, true,"", ""),
            new Data("SSome_Subsig_Lone", 0, false, true, false,false,"SSome", ""),
            new Data("SSome_Subsig_One", 1, false, true, false,false,"SSome", ""),
            new Data("SSome_Subsig_Some", 3, false, true, false,false,"SSome", ""),

            new Data("SSome_Subset_Lone", 0, true, false, false,false,"", "SSome"),
            new Data("SSome_Subset_One", 1, true, false, false,false,"", "SSome"),
            new Data("SSome_Subset_Some", 3, true, false, false,false,"", "SSome"),


            new Data("Object", 3, false, false, true,true,"", ""),
            new Data("Chicken", 1, false, true, false,false,"Object", ""),
            new Data("Farmer", 1, false, true, false,false,"Object", ""),
            new Data("Fox", 1, false, true, false,false, "Object", "")
            );

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        for (int index = 0; index < expectedResults.size(); index++) {
            assertEquals(expectedResults.get(index).scope, translation.signatures.get(index).scope);
            assertEquals(expectedResults.get(index).name, translation.signatures.get(index).name);
            assertEquals(expectedResults.get(index).isSubsig, translation.signatures.get(index).isSubsig);
            assertEquals(expectedResults.get(index).isSubset, translation.signatures.get(index).isSubset);
            assertEquals(expectedResults.get(index).isAbstract, translation.signatures.get(index).isAbstract);
            assertEquals(expectedResults.get(index).hasChildSubsig, translation.signatures.get(index).hasChildSubsig);
            assertEquals(expectedResults.get(index).parentName, translation.signatures.get(index).getParentName());
            assertEquals(expectedResults.get(index).parentNames, translation.signatures.get(index).getParentsName());
        }
    }

    @Test
    public void testWhenExpr_1() throws Exception {
        String dashModel = "abstract sig Object {} one sig SigA, SigB extends Object {} conc state StateA { " +
                "near: set Object far: set Object \n" +
                "trans trans_When_test_in { when SigA in near } \n" +
                "trans trans_When_test_not_in { when SigA not in near } \n" +
                "trans trans_When_test_unary_not_2 { when !(SigA not in near) }\n" +
                "trans trans_When_test_unequal { when SigA != SigB }\n" +
                "trans trans_When_test_unary_not_1 { when !(SigA) }\n" +
                "trans trans_When_test_unequal_bang {when !(SigA != SigB)} }";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");

        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<DashPythonTranslation.Transition> transitions = translation.getRootStates().get(0).getTransitions();
        assertEquals( 6,transitions.size());

        List<String> expectedString = Arrays.asList(
                "SigA in SS.StateA_near",
                "SigA not in SS.StateA_near",
                "not(SigA not in SS.StateA_near)",
                "SigA != SigB",
                "not(SigA)",
                "not(SigA != SigB)");

        for(int index = 0; index < transitions.size(); index++){
            assertEquals(expectedString.get(index), transitions.get(index).getGuardConditions().get(0));
        }
    }

    @Test
    public void testDoExpr_1() throws Exception {
        String dashModel = "abstract sig Object {} one sig SigA, SigB extends Object {} conc state StateA {near: set Object far: set Object direction: one Direction\n" +
                "trans trans_Do_assign_assign_without_brace_no { do far = far }\n" +
                "trans trans_Do_assign_assign_without_brace {do far' = far}\n" +
                "trans trans_Do_assign_assign_with_brace {do{ far' = far} }\n" +
                "trans trans_Do_assign_assign_union_2 {do{ far' = far + SigA} }\n" +
                "trans trans_Do_assign_assign_union_3 {do{ far' = far + SigA + SigB} }\n" +
                "trans trans_Do_assign_assign_union_3_paren_1 {do{ far' = (far + SigA) + SigB} }\n" +
                "trans trans_Do_assign_assign_union_3_paren_2 {do{ far' = far + (SigB + SigA)} }\n" +
                "trans trans_Do_assign_assign_subtract_2 {do{ far' = far - SigA} }\n" +
                "trans trans_Do_assign_assign_subtract_3 {do{ far' = far - SigA - SigB} }\n" +
                "trans trans_Do_assign_assign_subtract_3_paren_1 {do{ far' = (far - SigA) - SigB} }\n" +
                "trans trans_Do_assign_assign_subtract_3_paren_2 {do{ far' = far - (SigA - SigB)} }\n" +
                "trans trans_Do_assign_assign_4_paren {do{ far' = ((far + SigA) - (SigB - far))} }\n" +
                "}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");

        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<DashPythonTranslation.Transition> transitions = translation.getRootStates().get(0).getTransitions();
        assertEquals(12, transitions.size());

        List<String> expectedString = Arrays.asList(
                "SS.StateA_far == SS.StateA_far",
                "StateA_far_updated == SS.StateA_far",
                "StateA_far_updated == SS.StateA_far",
                "StateA_far_updated == SS.StateA_far + SigA",
                "StateA_far_updated == SS.StateA_far + SigA + SigB",
                "StateA_far_updated == SS.StateA_far + SigA + SigB",
                "StateA_far_updated == SS.StateA_far + (SigB + SigA)",
                "StateA_far_updated == SS.StateA_far - SigA",
                "StateA_far_updated == SS.StateA_far - SigA - SigB",
                "StateA_far_updated == SS.StateA_far - SigA - SigB",
                "StateA_far_updated == SS.StateA_far - (SigA - SigB)",
                "StateA_far_updated == SS.StateA_far + SigA - (SigB - SS.StateA_far)");

        for (int index = 0; index < transitions.size(); index++) {
            assertEquals(expectedString.get(index), transitions.get(index).getActions().get(0));
        }
    }

    @Test
    public void testRelations() throws Exception {
        class Data{
            public String name;
            public String types;
            public Data(String name, String types) {
                this.name = name;
                this.types = types;
            }
        }

        String dashModel =
                        "sig A1 {\n" +
                        "\tf0: one A1,\n" +
                        "    f1: lone A1\n" +
                        "}\n" +
                        "sig A2 {f2: some A1}\n" +
                        "sig A3 {f3: lone A1}\n" +
                        "sig A4 {f4: set A1}\n" +
                        "sig A5 {f5: A1 one -> lone A2}\n" +
                        "sig A6 {f6: A1 one -> lone A2 -> lone A3}";

        List<Data> expectedResults = Arrays.asList(
                new Data("f0", "[A1, A1]"),
                new Data("f1", "[A1, A1]"),
                new Data("f2", "[A2, A1]"),
                new Data("f3", "[A3, A1]"),
                new Data("f4", "[A4, A1]"),
                new Data("f5", "[A5, A1, A2]"),
                new Data("f6", "[A6, A1, A2, A3]")
        );

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        for (int index = 0; index < expectedResults.size(); index++) {
            assertEquals(expectedResults.get(index).name, translation.relations.get(index).name);
            assertEquals(expectedResults.get(index).types, translation.relations.get(index).types);
        }
    }
}
