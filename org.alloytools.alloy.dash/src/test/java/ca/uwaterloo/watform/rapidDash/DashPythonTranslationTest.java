package ca.uwaterloo.watform.rapidDash;


import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.junit.Test;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class DashPythonTranslationTest {
    private long findStateOccurncesInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getStates().stream().filter(state -> state.getName().equals(stateName)).count();
    }

    private DashPythonTranslation.State findStateInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getStates().stream().filter(state -> state.getName().equals(stateName)).findAny().get();
    }

    @Test
    public void testStates() throws Exception {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);
        assertEquals(1, translation.getStates().size());
        assertEquals("concState", translation.getStates().get(0).getName());

        List<DashPythonTranslation.State> secondary_states = translation.getStates().get(0).getSubstates();

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
    public void testTransitions() throws Exception {
        String dashModel = "conc state topConcStateA { event A{} default state s1{} state s2{} trans t1 {from s2 on A goto s1} trans t2 {from s1 on A goto s2} }";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);

        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        DashPythonTranslation.State topState = translation.getStates().get(0);
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
    public void testSignatures() throws Exception {
        String dashModel = "sig Floor {}\n" +
                "one sig Chicken {}\n" +
                "some sig SomeSig {}\n" +
                "lone sig LoneSig {}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);

        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        assertEquals(4, translation.signatures.size());
        assertEquals(translation.signatures.get(0).name, "Floor");
        assertEquals(translation.signatures.get(0).multiplicity, "set");
        assertEquals(translation.signatures.get(0).cardinality, 3);
        assertEquals(translation.signatures.get(1).name, "Chicken");
        assertEquals(translation.signatures.get(1).multiplicity, "one");
        assertEquals(translation.signatures.get(1).cardinality, 1);
        assertEquals(translation.signatures.get(2).name, "SomeSig");
        assertEquals(translation.signatures.get(2).multiplicity, "some");
        assertEquals(translation.signatures.get(2).cardinality, 3);
        assertEquals(translation.signatures.get(3).name, "LoneSig");
        assertEquals(translation.signatures.get(3).multiplicity, "lone");
        assertEquals(translation.signatures.get(3).cardinality, 1);
    }
}
