package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.AlloyProblem;
import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * A command processor which runs the Portus and Fortress translations but does not solve to check if Portus supports
 * a model.
 */
final class CheckSupportCommandProcessor implements CommandProcessor {

    private static final PortusOptions.FortressSmtSolver SOLVER = A4Options.SatSolver.CHECK_PORTUS_SUPPORT;

    @Override
    public boolean process(AlloyProblem problem) {
        PortusStatistics statistics = new PortusStatistics();
        problem.getOptions().solver = SOLVER;
        try {
            SOLVER.commandRunner().executeCommand(
                    new StdoutA4Reporter(problem.getPortusOptions().verbose), statistics,
                    problem.getSigs(), problem.getCommand(), problem.getOptions());
            System.out.println("Result: SUPPORTED.");
            if (problem.getPortusOptions().verbose) {
                statistics.printSummary(problem.getPortusOptions());
            }
            return true;
        } catch (Exception e) {
            System.out.println("Result: UNSUPPORTED.");
            if (problem.getPortusOptions().verbose) {
                e.printStackTrace();
                statistics.printSummary(problem.getPortusOptions());
            } else {
                System.out.println(e.getMessage());
                System.out.println("Rerun with -v for a full stack trace.");
            }
            return false;
        }
    }

    @Override
    public String displayName() {
        return "Check Support";
    }

}
