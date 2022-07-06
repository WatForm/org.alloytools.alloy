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
        String userInput = new String(new char[30]).replace("\0", "3" + System.lineSeparator());
        System.setIn(new ByteArrayInputStream(userInput.getBytes()));
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
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

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
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        List<String> expectedTranslation = Arrays.asList("class Floor(Signature):",
                "sig_objects = {\"Floor$0\", \"Floor$1\", \"Floor$2\"}",
                "class Medication(Signature):",
                "sig_objects = {\"Medication$0\", \"Medication$1\", \"Medication$2\"}",
                "class Chicken(Signature):",
                "sig_objects = {\"Chicken$0\"}",
                "class Farmer(Signature):",
                "sig_objects = {\"Farmer$0\"}",
                "class Fox(Signature):",
                "sig_objects = {\"Fox$0\"}",
                "class Grain(Signature):",
                "sig_objects = {\"Grain$0\"}",
                "class SomeSig(Signature):",
                "sig_objects = {\"SomeSig$0\", \"SomeSig$1\", \"SomeSig$2\"}",
                "class LoneSig(Signature):",
                "sig_objects = {}");

        CoreDashToPython.print(translation);

        for(String sigTrans : expectedTranslation){
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
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

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
}
