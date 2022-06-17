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
    public void testSignatures() throws IOException {
        String dashModel = "sig Floor {}\n" +
                "sig Medication {}\n" +
                "one sig Chicken, Farmer, Fox, Grain {}\n" +
                "some sig SomeSig {}\n" +
                "lone sig LoneSig {}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        List<String> expectedTranslation = Arrays.asList("Floor = Signature(\"Floor\", \"set\", 3)",
                "Medication = Signature(\"Medication\", \"set\", 3)",
                "Chicken = Signature(\"Chicken\", \"one\", 1)",
                "Farmer = Signature(\"Farmer\", \"one\", 1)",
                "Fox = Signature(\"Fox\", \"one\", 1)",
                "Grain = Signature(\"Grain\", \"one\", 1)",
                "SomeSig = Signature(\"SomeSig\", \"some\", 3)",
                "LoneSig = Signature(\"LoneSig\", \"lone\", 1)");

        for(String sigTrans : expectedTranslation){
            assert (CoreDashToPython.convert2String(translation).contains(sigTrans));
        }
    }
}
