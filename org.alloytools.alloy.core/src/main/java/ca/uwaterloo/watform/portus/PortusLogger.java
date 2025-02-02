package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.logging.EventLogger;
import fortress.modelfinders.ModelFinderResult;
import fortress.msfol.Theory;
import fortress.transformers.ProblemStateTransformer;
import fortress.util.Nanoseconds;

/**
 * Encapsulates all interaction with the A4Reporter system, and doubles as an EventLogger to log internal
 * Fortress events.
 */
public final class PortusLogger implements EventLogger {

    private final A4Reporter reporter;

    private long startTimeMs = 0;

    public PortusLogger(A4Reporter reporter) {
        this.reporter = reporter;
    }

    /** For passing to Alloy when an A4Reporter is required. */
    public A4Reporter getReporter() {
        return reporter;
    }

    /** Called when we're just about to begin the Alloy to Fortress translation. */
    public void translationStarted(String solver, int bitwidth, int maxseq) {
        // we have to call this to get accurate timing from the default reporter (even though it says "Generating CNF")
        reporter.translate(solver, bitwidth, maxseq, 0, 0, 0, 0, "fortress");
        startTimeMs = System.currentTimeMillis();
    }

    /** Called once we've finished translating to Fortress. */
    public void translationFinished(Theory theory) {
        // this will say "No translation information available", but we have to call it for accurate timing again
        // the metadata we could give it isn't applicable to SMT theories
        reporter.debug("Generated theory stats: " + formatTheoryStats(theory));
        reporter.solve(-1, -1, -1, -1);
    }

    @Override
    public void transformerStarted(ProblemStateTransformer transformer) {}

    @Override
    public void transformerFinished(ProblemStateTransformer transformer, Nanoseconds time) {
        reporter.debug("Ran transformer: " + transformer.name() + ". " + formatTime(time) + ".");
    }

    @Override
    public void allTransformersFinished(Theory finalTheory, Nanoseconds totalTime) {
        reporter.debug("All transformers finished. Total time: " + formatTime(totalTime) + ".");
        reporter.debug("Final theory stats: " + formatTheoryStats(finalTheory));
    }

    @Override
    public void invokingSolverStrategy() {
        reporter.debug("Opening SMT solver session...");
    }

    @Override
    public void convertingToSolverFormat() {}

    @Override
    public void convertedToSolverFormat(Nanoseconds time) {
        reporter.debug("Converted theory to solver format. " + formatTime(time) + ".");
    }

    @Override
    public void solving() {}

    @Override
    public void solverFinished(Nanoseconds time) {
        reporter.debug("Solved. SMT solver took " + formatTime(time) + ".");
    }

    @Override
    public void finished(ModelFinderResult result, Nanoseconds time) {
        new Exception().printStackTrace();
        reporter.debug("Finished. SMT result: " + result + ". Total Fortress time: " + formatTime(time) + ".");
    }

    @Override
    public void timeoutInternal() {}

    /** Called after all translation is done to output the final command. */
    public void outputResult(Command command, AlloySolution solution) {
        if (solution == null) {
            return; // ignore - possible for 'output to file' solvers
        }
        long totalTimeMs = System.currentTimeMillis() - startTimeMs;
        if (solution.satisfiable()) {
            reporter.resultSAT(command, totalTimeMs, solution);
        } else {
            reporter.resultUNSAT(command, totalTimeMs, solution);
        }
    }

    /** Called for 'output to file' solvers to output the filename. */
    public void outputFilename(String filename) {
        reporter.resultCNF(filename);
    }

    /** Output a message that Fortress supports this model. */
    public void outputHasFortressSupport() {
        reporter.debug("Fortress translation finished. Model is supported.");
    }

    private String formatTime(Nanoseconds time) {
        return time.toMilli().value() + "ms";
    }

    private String formatTheoryStats(Theory theory) {
        return theory.sorts().size() + " sorts, " +
                theory.functionDeclarations().size() + " functions, " +
                theory.axioms().size() + " axioms with " +
                PortusUtil.countSymbols(theory) + " symbols.";
    }

}
