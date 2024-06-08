package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * A command processor that checks correctness. Given a command, it generates an intepretation by going through Portus,
 * then ensures the interpretation is valid according to Kodkod. If Portus returns UNSAT, it ensures the command is
 * UNSAT according to Kodkod as well.
 */
final class CorrectnessCommandProcessor implements CommandProcessor {

    private final CorrectnessChecker correctnessChecker;

    public CorrectnessCommandProcessor(CorrectnessChecker correctnessChecker) {
        this.correctnessChecker = correctnessChecker;
    }

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        PortusStatistics statistics = new PortusStatistics();
        CorrectnessChecker.Result result = correctnessChecker.checkCorrectness(
                statistics, world, command, options);

        if (result.kind == CorrectnessChecker.Result.Kind.EXCEPTION) {
            assert result.exception != null;
            System.err.println("ERROR: Exception! " + result.exception.getMessage().replace('\n', ' '));
            result.exception.printStackTrace();
            return false;
        }
        assert result.fortressSolution != null;

        System.out.println("Portus result: " + (result.fortressSolution.satisfiable() ? "SAT" : "UNSAT"));
        if (result.fortressSolution.satisfiable()) {
            System.out.println("Portus interpretation:");
            System.out.println(result.fortressSolution.format());
        }
        if (result.kind.isError) {
            System.err.print("ERROR: ");
        }
        System.out.println(result.kind.description);
        statistics.printSummary(options.portusOptions);
        return !result.kind.isError;
    }

    @Override
    public String displayName() {
        return "Correctness";
    }

}
