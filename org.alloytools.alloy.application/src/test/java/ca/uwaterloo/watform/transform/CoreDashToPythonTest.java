package ca.uwaterloo.watform.transform;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

public class CoreDashToPythonTest {
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

        List<String> expectedTranslation = Arrays.asList("Floor = Signature(\"Floor\", \"set\", 3, False, {}, False, None, False)\n",
                "Medication = Signature(\"Medication\", \"set\", 3, False, {}, False, None, False)\n",
                "Chicken = Signature(\"Chicken\", \"one\", 1, False, {}, False, None, False)\n",
                "Farmer = Signature(\"Farmer\", \"one\", 1, False, {}, False, None, False)\n",
                "Fox = Signature(\"Fox\", \"one\", 1, False, {}, False, None, False)\n",
                "Grain = Signature(\"Grain\", \"one\", 1, False, {}, False, None, False)\n",
                "SomeSig = Signature(\"SomeSig\", \"some\", 3, False, {}, False, None, False)\n",
                "LoneSig = Signature(\"LoneSig\", \"lone\", 1, False, {}, False, None, False)");

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

        List<String> expectedTranslation = Arrays.asList("A = Signature(\"A\", \"set\", 3, False, {}, False, None, False)",
                "Asubset1 = Signature(\"Asubset1\", \"set\", 3, False, {}, True, A, False)",
                "Asubset2 = Signature(\"Asubset2\", \"set\", 3, False, {}, True, A, False)",
                "AAsubset1 = Signature(\"AAsubset1\", \"set\", 3, False, {}, True, Asubset1, False)",
                "E = Signature(\"E\", \"set\", 3, False, {}, True, A, False)",
                "B = Signature(\"B\", \"set\", 3, False, {}, False, None, False)",
                "C = Signature(\"C\", \"set\", 3, True, {A,B}, False, None, False)",
                "D = Signature(\"D\", \"set\", 3, True, {C,A}, False, None, False)");

        for(String sigTrans : expectedTranslation){
            assert (CoreDashToPython.convert2String(translation).contains(sigTrans));
        }
    }
}
