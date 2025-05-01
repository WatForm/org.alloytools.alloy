package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.FortressSolution;
import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;

final class RunCommandProcessor implements CommandProcessor {

    private final A4Options.SatSolver solver;

    public RunCommandProcessor(A4Options.SatSolver solver) {
        this.solver = solver;
    }

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        // Run with statistics if this solver is a Portus solver
        // TODO: this is an ugly hack, fix it somehow
        boolean isPortus = solver instanceof PortusOptions.FortressSmtSolver;
        PortusStatistics statistics = new PortusStatistics();

        AlloySolution solution = null;
        try {
            if (isPortus) {
                solution = ((PortusOptions.FortressSmtSolver) solver).commandRunner().executeCommand(
                        new StdoutA4Reporter(options.portusOptions.verbose), statistics, world, command, options);
            } else {
                solution = solver.commandRunner().executeCommand(A4Reporter.NOP, world, command, options);
            }
            System.out.println("Result: " + (solution.satisfiable() ? "SAT" : "UNSAT"));
            if (options.portusOptions.verbose && solution.satisfiable()) {
                System.out.println("Interpretation:");
                System.out.println(solution.format());
            }
        } catch (Exception e) {
            System.out.println("Result: exception");
            e.printStackTrace();
            statistics.printSummary(options.portusOptions);
            return false;
        } finally {
            if (isPortus && solution != null) {
                ((FortressSolution) solution).close(); // TODO better resource management
            }
        }

        if (options.portusOptions.verbose) {
            statistics.printSummary(options.portusOptions);
        }
        return true;
    }

    @Override
    public String displayName() {
        return "Run " + solver.id();
    }

}
