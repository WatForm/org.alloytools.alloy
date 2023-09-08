package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

/**
 * A command processor that checks correctness. Given a command, it generates an intepretation by going through Portus,
 * then ensures the interpretation is valid according to Kodkod. If Portus returns UNSAT, it ensures the command is
 * UNSAT according to Kodkod as well.
 */
final class CorrectnessCommandProcessor implements CommandProcessor {

    private final CorrectnessChecker correctnessChecker = new CorrectnessChecker();

    @Override
    public void process(Iterable<Sig> sigs, Command command, A4Options options) {
        try {
            CorrectnessChecker.Result result = correctnessChecker.checkCorrectness(sigs, command, options);
            System.out.println("Portus result: " + (result.fortressSolution.satisfiable() ? "SAT" : "UNSAT"));
            if (result.fortressSolution.satisfiable()) {
                System.out.println("Portus interpretation: " + result.fortressSolution.format());
            }
            if (result.kind.isError) {
                System.err.println("ERROR: " + result.kind.description);
            } else {
                System.out.println(result.kind.description);
            }
        } catch (Exception e) {
            System.err.println("ERROR: Exception!");
            e.printStackTrace();
        }
    }

    @Override
    public String displayName() {
        return "Correctness";
    }

}
