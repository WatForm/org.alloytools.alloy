/**
 * Test the data populated to the Velocity template.
 */

package ca.uwaterloo.watform.transform;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

public class CoreDashToPythonTest {

    private InputStream sysInBackup;
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

    // right now this is just a sanity check
    @Test
    public void testStates() throws IOException {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        assertNotNull(CoreDashToPython.convert2String(translation));
    }

    @Test
    public void testSignaturesMultiplicity() throws IOException {
        String dashModel = "sig Floor {}\n" +
                "sig Medication {}\n" +
                "one sig Chicken, Farmer, Fox, Grain {}\n" +
                "some sig SomeSig {}\n" +
                "lone sig LoneSig {}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList("class Floor(Signature):",
                "atoms = {\"Floor$0\", \"Floor$1\", \"Floor$2\"}",
                "class Medication(Signature):",
                "atoms = {\"Medication$0\", \"Medication$1\", \"Medication$2\"}",
                "class Chicken(Signature):",
                "atoms = {\"Chicken$0\"}",
                "class Farmer(Signature):",
                "atoms = {\"Farmer$0\"}",
                "class Fox(Signature):",
                "atoms = {\"Fox$0\"}",
                "class Grain(Signature):",
                "atoms = {\"Grain$0\"}",
                "class SomeSig(Signature):",
                "atoms = {\"SomeSig$0\", \"SomeSig$1\", \"SomeSig$2\"}",
                "class LoneSig(Signature):",
                "atoms = set()");

        for(String sigTrans : expectedTranslation){
            // System.out.println("====== "+sigTrans);
            assert (CoreDashToPython.convert2String(translation).contains(sigTrans));
        }
    }

    @Test
    public void testSignaturesSubsetsRelationship() throws IOException {
        String dashModel = "sig Asubset1, Asubset2 extends A {}\n" +
        "sig AAsubset1 extends Asubset1 {}\n" +
        "sig C in A + B {}\n" +
        "sig D in C + A {}\n" +
        "sig E extends A {}\n" +
        "sig A {}\n" +
        "sig B {}\n";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList("class Asubset1(Signature):",
                "class Asubset2(Signature):",
                "class AAsubset1(Signature):",
                "class C(Signature):",
                "class D(Signature):",
                "class E(Signature):",
                "class A(Signature):",
                "class B(Signature):");

        for(String sigTrans : expectedTranslation){
            assert (CoreDashToPython.convert2String(translation).contains(sigTrans));
        }
    }

    @Test
    public void testRelations() throws IOException {
        String dashModel = "sig A1 {\n" +
                "\tf0: one A1,\n" +
                "    f1: lone A1\n" +
                "}\n" +
                "sig A2 {f2: some A1}\n" +
                "sig A3 {f3: lone A1}\n" +
                "sig A4 {f4: set A1}\n" +
                "sig A5 {f5: A1 one -> lone A2}\n" +
                "sig A6 {f6: A1 one -> lone A2 -> lone A3}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList("class f0(Relation):",
                "class f1(Relation):",
                "class f2(Relation):",
                "class f3(Relation):",
                "class f4(Relation):",
                "class f5(Relation):",
                "class f6(Relation):");

        for(String trans : expectedTranslation){
            assert (CoreDashToPython.convert2String(translation).contains(trans));
        }
    }

    @Test
    public void test_GuardCondition_ConcatenationAndFormat_Correct() throws IOException {
        String dashModel = "sig Med {}\n" +
                "conc state S {\n" +
                "    default state R{\n" +
                "        env in_m1, in_m2: lone Med\n" +
                "        med: set Med\n" +
                "        interactions: Med -> set Med\n"+
                "        trans add_med1 {\n" +
                "            when {\n" +
                "                (!(in_m1 in med) and !(in_m1 in med))\n" +
                "                in_m1 in med or in_m1 in med\n" +
                "            }\n" +
                "            do med' = med\n" +
                "        }\n" +
                "        trans add_med2 {\n" +
                "            when (!(in_m1 in med) and !(in_m1 in med))\n" +
                "            do med' = med\n" +
                "        }\n" +
                "        trans add_med3 {\n" +
                "            when (in_m1 in med) and !(in_m1 in med)\n" +
                "            do med' = med\n" +
                "        }\n" +
                "        trans add_med4 {\n" +
                "            when {\n" +
                "                (in_m1 in med) and !(in_m1 in med) or\n" +
                "                (in_m1 in med) or !(in_m1 in med)\n" +
                "            }\n" +
                "            do med' = med\n" +
                "        }\n" +
                "        trans add_med5 {\n" +
                "            when {\n" +
                "                (in_m1 in med) and !(in_m1 in med) or\n" +
                "                (in_m1 in med) or !(in_m1 in med) and\n" +
                "                (in_m1 in med) and !(in_m1 in med)\n" +
                "            }\n" +
                "            do med' = med\n" +
                "        }\n" +
                "        trans add_relation {\n" +
                "            when {\n" +
                "                (!(in_m1 -> in_m2 in interactions) and !(in_m2 -> in_m1 in interactions))\n" +
                "                in_m1 in med\n" +
                "                in_m2 in med\n" +
                "            }\n" +
                "            do interactions' = interactions + {in_m1->in_m2 + in_m2->in_m1}\n" +
                "        }\n"+
                "    }\n" +
                "}\n";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList(
                "if not (not(SS.S_R_in_m1 in SS.S_R_med) and",  // add_med1
                "not(SS.S_R_in_m1 in SS.S_R_med) and",
                "(SS.S_R_in_m1 in SS.S_R_med or",
                "SS.S_R_in_m1 in SS.S_R_med)):",
                "if not (not(SS.S_R_in_m1 in SS.S_R_med) and",  // add_med2
                "not(SS.S_R_in_m1 in SS.S_R_med)):",
                "if not (SS.S_R_in_m1 in SS.S_R_med and",       // add_med3
                "not(SS.S_R_in_m1 in SS.S_R_med)):",
                "if not ((SS.S_R_in_m1 in SS.S_R_med and",      // add_med4
                "not(SS.S_R_in_m1 in SS.S_R_med)) or",
                "SS.S_R_in_m1 in SS.S_R_med or",
                "not(SS.S_R_in_m1 in SS.S_R_med)):",
                "if not ((SS.S_R_in_m1 in SS.S_R_med and",      // add_med5
                "not(SS.S_R_in_m1 in SS.S_R_med)) or",
                "SS.S_R_in_m1 in SS.S_R_med or",
                "(not(SS.S_R_in_m1 in SS.S_R_med) and",
                "SS.S_R_in_m1 in SS.S_R_med and",
                "not(SS.S_R_in_m1 in SS.S_R_med))):",
                "if not (not(SS.S_R_in_m1 * SS.S_R_in_m2 in SS.S_R_interactions) and", // add_relation
                "not(SS.S_R_in_m2 * SS.S_R_in_m1 in SS.S_R_interactions) and",
                "SS.S_R_in_m1 in SS.S_R_med and",
                "SS.S_R_in_m2 in SS.S_R_med):"
        );

        String output = CoreDashToPython.convert2String(translation);

        for(String trans : expectedTranslation){
            assert (output.contains(trans));
        }
    }

    @Test
    public void test_EqualSign_ConditionsAndActions_Correct() throws IOException {
        String dashModel = "sig Medication {} conc state S {" +
                "    env in_m1, in_m2: lone Medication" +
                "    env in_m3: set Medication" +
                "    m2, m1, m4: set Medication" +
                "    m3: lone Medication" +
                "    init {no in_m1 no in_m2 no in_m3 no m1 no m2 no m3 no m4}" +
                "    invariant equal {in_m1 = in_m2 or m1 = m2 and in_m1 = in_m2 and in_m3 = in_m2}" +
                "    trans t1 {when {in_m1 = in_m2 or" +
                "            m1 = m2 and in_m1 = in_m2}" +
                "        do{in_m1 = in_m2 + in_m1" +
                "            m1' = m2 + m1 + m4}}" +
                "    trans t2 {when {in_m1 + in_m3 = in_m2\n" +
                "            m4 + m1 = m2 + m3} do{in_m2 = in_m1 + in_m2" +
                "            m2' = m1}}}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList(
                "SS.S_in_m1 = Medication",  // Equal sign in init
                "SS.S_m2 = Medication",
                "SS.S_in_m1 == SS.S_in_m2 or",  // Equal sign in guard 1
                "(SS.S_m1 == SS.S_m2 and",
                "SS.S_in_m1 == SS.S_in_m2))",
                "SS.S_in_m1 = SS.S_in_m2 + SS.S_in_m1",  // Equal sign in action 1
                "SS.S_m1 = SS.S_m2 + SS.S_m1 + SS.S_m4"
        );

        String output = CoreDashToPython.convert2String(translation);

        for(String trans : expectedTranslation){
            assert (output.contains(trans));
        }
    }

    @Test
    public void test_QuantifiedExpressions_Correct() throws IOException {
        String dashModel = "sig Patient {} sig Medication {} conc state EHealthSystem { medications: set Medication " +
                "patients: set Patient prescriptions: Patient -> set Medication interactions: Medication -> set Medication " +
                "invariant I_2_Types_1 { all m1, m2: medications, p: patients | m1 -> m2 in interactions and p in Patient}" +
                "invariant I_2_Same_Type { all m1, m2: Medication | m1 -> m2 in interactions}" +
                "invariant I_3_Same_type { all m1, m2, m3: Medication | m1 -> m2 in interactions and m2 -> m3 in interactions}" +
                "invariant I_symmetry { all m1, m2: Medication | m1 -> m2  in interactions iff m2 -> m1 in interactions }" +
                "invariant I_no_statement {all m: medications | not (m -> m in interactions)}" +
                "invariant I_2_Types_2 { all m1, m2: medications, p: patients | m1 -> m2 in interactions => !((p -> m1 in prescriptions) and (p -> m2 in prescriptions))}" +
                "trans add_interaction {do interactions' = interactions} init {no medications no prescriptions no patients no interactions}}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList(
            "(all([(m1 * m2 in SS.EHealthSystem_interactions and p in Patient) for m1 in SS.EHealthSystem_medications for m2 in SS.EHealthSystem_medications for p in SS.EHealthSystem_patients]))",
            "(all([m1 * m2 in SS.EHealthSystem_interactions for m1 in Medication for m2 in Medication]))",
            "(all([(m1 * m2 in SS.EHealthSystem_interactions and m2 * m3 in SS.EHealthSystem_interactions) for m1 in Medication for m2 in Medication for m3 in Medication]))",
            "(all([(m1 * m2 in SS.EHealthSystem_interactions) == (m2 * m1 in SS.EHealthSystem_interactions) for m1 in Medication for m2 in Medication]))",
            "(all([not(m * m in SS.EHealthSystem_interactions) for m in SS.EHealthSystem_medications]))",
            "(all([(p * m1 in SS.EHealthSystem_prescriptions and p * m2 in SS.EHealthSystem_prescriptions) for m1 in SS.EHealthSystem_medications for m2 in SS.EHealthSystem_medications for p in SS.EHealthSystem_patients]))"
            );

        String output = CoreDashToPython.convert2String(translation);

        for(String trans : expectedTranslation){
            assert (output.contains(trans));
        }
    }

    @Test
    public void test_Quantifers_Correct() throws IOException {
        String dashModel = "sig Patient {} sig Medication {} conc state EHealthSystem {patients: set Patient\ninteractions: Medication -> set Medication\n" +
                "trans interaction_test_1 {\n" +
                "when{no interactions\n" +
                "some interactions\n" +
                "lone interactions\n" +
                "one interactions}\n" +
                "do interactions' = interactions}" +
                "trans interaction_test_2 {\n" +
                "when{no patients\n" +
                "some patients\n" +
                "lone patients\n" +
                "one patients}\n" +
                "do interactions' = interactions}}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        dashModule = new DashToCoreDash().transformToCoreDash(dashModule, null, "");
        DashPythonTranslation translation = new DashPythonTranslation(dashModule, null);

        List<String> expectedTranslation = Arrays.asList(
                "not bool(SS.EHealthSystem_interactions)",
                "bool(SS.EHealthSystem_interactions)",
                "(1 >= len(SS.EHealthSystem_interactions))",
                "(1 == len(SS.EHealthSystem_interactions))",
                "not bool(SS.EHealthSystem_patients)",
                "bool(SS.EHealthSystem_patients)",
                "(1 >= len(SS.EHealthSystem_patients))",
                "(1 == len(SS.EHealthSystem_patients))"
        );


        String output = CoreDashToPython.convert2String(translation);
        System.out.println(output);

        for(String trans : expectedTranslation){
            assert (output.contains(trans));
        }
    }
}
