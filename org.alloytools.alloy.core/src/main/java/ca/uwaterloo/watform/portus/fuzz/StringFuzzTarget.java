package ca.uwaterloo.watform.portus.fuzz;

import ca.uwaterloo.watform.portus.cli.CorrectnessChecker;
import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;

@SuppressWarnings("unused")
public class StringFuzzTarget {

    public static void fuzzerTestOneInput(FuzzedDataProvider data) {
        String alloy = data.consumeRemainingAsAsciiString();
        try {
            Module world = CompUtil.parseEverything_fromString(null, alloy);
            if (world.getAllCommands().isEmpty()) {
                return;
            }

            CorrectnessChecker correctness = new CorrectnessChecker();
            Iterable<Sig> sigs = world.getAllReachableSigs();
            Command command = world.getAllCommands().get(0);
            A4Options options = new A4Options();

            CorrectnessChecker.Result result = correctness.checkCorrectness(sigs, command, options);
            if (result.kind == CorrectnessChecker.Result.Kind.KODKOD_SAT_FORTRESS_UNSAT
                || result.kind == CorrectnessChecker.Result.Kind.FORTRESS_INTERPRETATION_INVALID) {
                throw new RuntimeException();
            }
        } catch (ErrorSyntax syntax) {
            // not an error for fuzz testing
        }
    }

}
