package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.AlloyProblem;
import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;

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
    public boolean process(AlloyProblem problem) {
        PortusStatistics statistics = new PortusStatistics();
        try {
            solver.commandRunner().translate(statistics, problem); // ignore the result
        } catch (Exception e) {
            System.err.println("Exception during translation!");
            e.printStackTrace();
            statistics.printSummary(problem.getPortusOptions());
            return false;
        }
        statistics.printSummary(problem.getPortusOptions());
        return true;
    }

    @Override
    public String displayName() {
        return "Translate and Get Statistics";
    }

}
