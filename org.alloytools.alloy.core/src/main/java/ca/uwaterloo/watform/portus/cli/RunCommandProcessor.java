package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.AlloyProblem;
import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;

final class RunCommandProcessor implements CommandProcessor {

    private final A4Options.SatSolver solver;

    public RunCommandProcessor(A4Options.SatSolver solver) {
        this.solver = solver;
    }

    @Override
    public boolean process(AlloyProblem problem) {
        // Run with statistics if this solver is a Portus solver
        // TODO: this is an ugly hack, fix it somehow
        boolean isPortus = solver instanceof PortusOptions.FortressSmtSolver;
        PortusStatistics statistics = new PortusStatistics();

        try {
            AlloySolution solution;
            if (isPortus) {
                solution = ((PortusOptions.FortressSmtSolver) solver).commandRunner().executeCommand(
                        new StdoutA4Reporter(problem.getPortusOptions().verbose), statistics,
                        problem.getSigs(), problem.getCommand(), problem.getOptions());
            } else {
                solution = solver.commandRunner().executeCommand(
                        A4Reporter.NOP, problem.getSigs(), problem.getCommand(), problem.getOptions());
            }
            System.out.println("Result: " + (solution.satisfiable() ? "SAT" : "UNSAT"));
            if (problem.getPortusOptions().verbose && solution.satisfiable()) {
                System.out.println("Interpretation:");
                System.out.println(solution.format());
            }
        } catch (Exception e) {
            System.out.println("Result: exception");
            e.printStackTrace();
            statistics.printSummary(problem.getPortusOptions());
            return false;
        }

        if (problem.getPortusOptions().verbose) {
            statistics.printSummary(problem.getPortusOptions());
        }
        return true;
    }

    @Override
    public String displayName() {
        return "Run " + solver.id();
    }

}
