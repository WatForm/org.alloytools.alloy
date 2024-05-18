package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.deltadebug.AlloyDeltaDebugger;
import ca.uwaterloo.watform.portus.deltadebug.AlloyInput;
import ca.uwaterloo.watform.portus.deltadebug.Indicator;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.file.FileSystems;

final class DeltaDebugCommandProcessor implements CommandProcessor {

    private static final String MINIMIZED_ALLOY_EXTENSION = ".minimized.als";

    private final CorrectnessChecker correctnessChecker = new CorrectnessChecker();
    private final AlloyDeltaDebugger deltaDebugger = new AlloyDeltaDebugger();

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        AlloyInput initialInput = new AlloyInput(world, command, options);
        System.out.println("Running for initial result: " + initialInput);
        CorrectnessChecker.Result initialResult = correctnessChecker.checkCorrectness(world, command, options);
        System.out.println("Initial result: " + initialResult);

        Indicator indicator = input -> {
            System.out.println("Running mutation: " + input);
            CorrectnessChecker.Result result = correctnessChecker.checkCorrectness(
                    input.world, input.command, input.options);
            System.out.println("Result: " + result + " (expected: " + initialResult + ")");
            if (result.kind == CorrectnessChecker.Result.Kind.EXCEPTION) {
                assert result.exception != null;
                System.out.print("Exception: ");
                result.exception.printStackTrace();
            }
            System.out.println("Model:");
            try {
                StringWriter writer = new StringWriter();
                input.writeAlloy(writer);
                System.out.print(writer);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
            return result.kind == initialResult.kind;
        };

        AlloyInput minimized = deltaDebugger.deltaDebug(indicator, initialInput);
        System.out.println("Minimized: " + minimized);

        // Write to the specified file
        File file = options.portusOptions.createOutputFile(MINIMIZED_ALLOY_EXTENSION);
        try (Writer writer = new FileWriter(file)) {
            minimized.writeAlloy(writer);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        System.out.println("Minimized model written to: " + options.portusOptions.outputDirectory
                + FileSystems.getDefault().getSeparator()
                + options.portusOptions.outputName
                + MINIMIZED_ALLOY_EXTENSION);
        return true;
    }

    @Override
    public String displayName() {
        return "Delta Debugging";
    }

}
