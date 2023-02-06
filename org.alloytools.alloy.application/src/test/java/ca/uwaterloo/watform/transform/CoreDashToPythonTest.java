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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

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
                "atoms = {}");

        CoreDashToPython.print(translation);

        for(String sigTrans : expectedTranslation){
            System.out.println("====== "+sigTrans);
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
}
