package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.deltadebug.AlloyDeltaDebugger;
import ca.uwaterloo.watform.portus.deltadebug.AlloyInput;
import ca.uwaterloo.watform.portus.deltadebug.Indicator;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

final class DeltaDebugCommandProcessor implements CommandProcessor {

    private final CorrectnessChecker correctnessChecker = new CorrectnessChecker();
    private final AlloyDeltaDebugger deltaDebugger = new AlloyDeltaDebugger();

    @Override
    public void process(Iterable<Sig> sigs, Command command, A4Options options) {
        AlloyInput initialInput = new AlloyInput(sigs, command, options);
        System.out.println("Running for initial result: " + initialInput);
        CorrectnessChecker.Result initialResult = correctnessChecker.checkCorrectness(sigs, command, options);
        System.out.println("Initial result: " + initialResult);

        Indicator indicator = input -> {
            System.out.println("Running mutation: " + input);
            CorrectnessChecker.Result result = correctnessChecker.checkCorrectness(
                    input.sigs, input.command, input.options);
            System.out.println("Result: " + result + " (expected: " + initialResult + ")");
            return result.kind == initialResult.kind;
        };

        AlloyInput minimized = deltaDebugger.deltaDebug(indicator, initialInput);

        // TODO: it would be best to write to a new Alloy file, but that's nontrivial from an AlloyInput
        System.out.println("Minimized: " + minimized);
    }

    @Override
    public String displayName() {
        return "Delta Debugging";
    }

}
