package ca.uwaterloo.watform.transform;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.junit.Test;

import java.io.IOException;

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

        assertNotNull(CoreDashToPython.toString(translation));
    }

    @Test
    public void testSignatures() throws IOException {
        String dashModel = "sig Floor {}\n" +
                "sig Medication {}\n" +
                "one sig Chicken, Farmer, Fox, Grain {}\n" +
                "some sig SomeSig {}\n" +
                "lone sig LoneSig {}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        String expectedTranslation = "Floor = Signature(\"Floor\", \"set\", 3)\n" +
                "Medication = Signature(\"Medication\", \"set\", 3)\n" +
                "Chicken = Signature(\"Chicken\", \"one\", 1)\n" +
                "Farmer = Signature(\"Farmer\", \"one\", 1)\n" +
                "Fox = Signature(\"Fox\", \"one\", 1)\n" +
                "Grain = Signature(\"Grain\", \"one\", 1)\n" +
                "SomeSig = Signature(\"SomeSig\", \"some\", 3)\n" +
                "LoneSig = Signature(\"LoneSig\", \"lone\", 1)";
        assert (CoreDashToPython.toString(translation).contains(expectedTranslation));
    }
}
