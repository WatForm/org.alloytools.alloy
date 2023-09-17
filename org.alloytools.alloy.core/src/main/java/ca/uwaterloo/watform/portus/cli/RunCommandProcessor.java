package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;
import edu.mit.csail.sdg.translator.CommandRunner;

final class RunCommandProcessor implements CommandProcessor {

    private final A4Options.SatSolver solver;

    public RunCommandProcessor(A4Options.SatSolver solver) {
        this.solver = solver;
    }

    @Override
    public boolean process(Iterable<Sig> sigs, Command command, A4Options options) {
        // Run with statistics if this solver if a Portus solver
        // TODO: this is an ugly hack, fix it somehow
        boolean isPortus = solver instanceof PortusOptions.FortressSmtSolver;
        PortusStatistics statistics = new PortusStatistics();

        CommandRunner runner;
        if (isPortus) {
            runner = ((PortusOptions.FortressSmtSolver) solver).commandRunnerWithStatistics(statistics);
        } else {
            runner = solver.commandRunner();
        }

        // TODO: time it - that should be done by PortusStatistics, I think, or a separate Stopwatch

        try {
            AlloySolution solution = runner.executeCommand(A4Reporter.NOP, sigs, command, options);
            System.out.println("Result: " + (solution.satisfiable() ? "SAT" : "UNSAT"));
            if (solution.satisfiable()) {
                System.out.println("Interpretation:");
                System.out.println(solution.format());
            }
        } catch (Exception e) {
            System.out.println("Result: exception");
            e.printStackTrace();
            statistics.printSummary();
            return false;
        }

        statistics.printSummary();
        return true;
    }

    @Override
    public String displayName() {
        return "Run " + solver.id();
    }

}
