package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.FortressSolution;
import ca.uwaterloo.watform.portus.PortusOptions;
import ca.uwaterloo.watform.portus.PortusStatistics;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * A command processor which runs the Portus and Fortress translations but does not solve to check if Portus supports
 * a model.
 */
final class CheckSupportCommandProcessor implements CommandProcessor {

    private static final PortusOptions.FortressSmtSolver SOLVER = A4Options.SatSolver.CHECK_PORTUS_SUPPORT;

    @Override
    public boolean process(Module world, Command command, A4Options options) {
        PortusStatistics statistics = new PortusStatistics();
        options.solver = SOLVER;
        try (FortressSolution ignored = SOLVER.commandRunner().executeCommand(
                new StdoutA4Reporter(options.portusOptions.verbose), statistics, world, command, options)) {
            System.out.println("Result: SUPPORTED.");
            if (options.portusOptions.verbose) {
                statistics.printSummary(options.portusOptions);
            }
            return true;
        } catch (Exception e) {
            System.out.println("Result: UNSUPPORTED.");
            if (options.portusOptions.verbose) {
                e.printStackTrace();
                statistics.printSummary(options.portusOptions);
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
