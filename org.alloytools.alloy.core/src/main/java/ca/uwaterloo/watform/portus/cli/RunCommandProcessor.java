package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusSATFactory;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.AlloySolution;
import kodkod.engine.satlab.SATFactory;

final class RunCommandProcessor implements CommandProcessor {

    private final SATFactory solver;

    public RunCommandProcessor(SATFactory solver) {
        this.solver = solver;
    }

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        // Run with statistics if this solver is a Portus solver
        boolean isPortus = solver instanceof PortusSATFactory;
        options.solver = solver;
        PortusStatistics statistics = new PortusStatistics();

        try {
            AlloySolution solution;
            if (isPortus) {
                solution = ((PortusSATFactory) solver).getCommandRunner().executeCommand(
                        new StdoutA4Reporter(options.portusOptions.verbose), statistics, world, command, options);
            } else {
                solution = options.commandRunner().executeCommand(A4Reporter.NOP, world, command, options);
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
