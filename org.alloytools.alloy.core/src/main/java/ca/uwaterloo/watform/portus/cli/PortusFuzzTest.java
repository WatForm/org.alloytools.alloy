package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

public class PortusFuzzTest {

    public void autofuzz(Iterable<Sig> sigs, Command command, A4Options options) {
        if (sigs == null || command == null || options == null) {
            return;
        }
        CorrectnessChecker correctness = new CorrectnessChecker();
        CorrectnessChecker.Result result = correctness.checkCorrectness(sigs, command, options);
        if (result.kind != CorrectnessChecker.Result.Kind.OK) {
            throw new RuntimeException();
        }
    }

}
