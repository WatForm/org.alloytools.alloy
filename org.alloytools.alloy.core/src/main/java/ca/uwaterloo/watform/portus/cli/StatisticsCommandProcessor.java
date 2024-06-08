package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * A command processor which runs the Portus translation and prints statistics on the generated Fortress theory without
 * running the SMT solver.
 */
final class StatisticsCommandProcessor implements CommandProcessor {

    private final PortusOptions.FortressSmtSolver solver;

    public StatisticsCommandProcessor(PortusOptions.FortressSmtSolver solver) {
        this.solver = solver;
    }

    public StatisticsCommandProcessor() {
        this(CorrectnessChecker.DEFAULT_FORTRESS_SOLVER);
    }

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        PortusStatistics statistics = new PortusStatistics();
        try {
            solver.commandRunner().translate(statistics, world, command, options); // ignore the result
        } catch (Exception e) {
            System.err.println("Exception during translation!");
            e.printStackTrace();
            statistics.printSummary(options.portusOptions);
            return false;
        }
        statistics.printSummary(options.portusOptions);
        return true;
    }

    @Override
    public String displayName() {
        return "Translate and Get Statistics";
    }

}
