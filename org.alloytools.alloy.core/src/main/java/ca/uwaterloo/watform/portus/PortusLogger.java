package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.logging.EventLogger;
import fortress.modelfind.ModelFinderResult;
import fortress.msfol.AndList;
import fortress.msfol.App;
import fortress.msfol.BitVectorLiteral;
import fortress.msfol.BuiltinApp;
import fortress.msfol.Closure;
import fortress.msfol.Distinct;
import fortress.msfol.DomainElement;
import fortress.msfol.EnumValue;
import fortress.msfol.Eq;
import fortress.msfol.Exists;
import fortress.msfol.Forall;
import fortress.msfol.IfThenElse;
import fortress.msfol.Iff;
import fortress.msfol.Implication;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Not;
import fortress.msfol.OrList;
import fortress.msfol.Quantifier;
import fortress.msfol.ReflexiveClosure;
import fortress.msfol.Term;
import fortress.msfol.TermVisitor;
import fortress.msfol.Theory;
import fortress.msfol.Var;
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
        // TODO: some stats about the final theory
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

    private String formatTime(Nanoseconds time) {
        return time.toMilli().value() + "ms";
    }

    private String formatTheoryStats(Theory theory) {
        return theory.sorts().size() + " sorts, " +
                theory.functionDeclarations().size() + " functions, " +
                theory.axioms().size() + " axioms with " +
                new CountSymbolsVisitor().countAxiomSymbols(theory) + " symbols.";
    }

    /** A visitor which naively counts the symbols in a term/theory. */
    private static class CountSymbolsVisitor implements TermVisitor<Integer> {

        public int countAxiomSymbols(Theory theory) {
            return sumVisits(theory.axioms());
        }

        @Override
        public Integer visitTop() {
            return 1;
        }

        @Override
        public Integer visitBottom() {
            return 1;
        }

        @Override
        public Integer visitVar(Var term) {
            return 1;
        }

        @Override
        public Integer visitEnumValue(EnumValue term) {
            return 1;
        }

        @Override
        public Integer visitDomainElement(DomainElement term) {
            return 1;
        }

        @Override
        public Integer visitNot(Not term) {
            return 1 + visit(term.body());
        }

        @Override
        public Integer visitAndList(AndList term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitOrList(OrList term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitDistinct(Distinct term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitImplication(Implication term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitIff(Iff term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitEq(Eq term) {
            return 1 + visit(term.left()) + visit(term.right());
        }

        @Override
        public Integer visitApp(App term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitBuiltinApp(BuiltinApp term) {
            return 1 + sumVisits(term.arguments());
        }

        @Override
        public Integer visitExists(Exists term) {
            return visitQuantifier(term);
        }

        @Override
        public Integer visitForall(Forall term) {
            return visitQuantifier(term);
        }

        private Integer visitQuantifier(Quantifier term) {
            return 1 + term.vars().size() + visit(term.body());
        }

        @Override
        public Integer visitIntegerLiteral(IntegerLiteral term) {
            return 1;
        }

        @Override
        public Integer visitBitVectorLiteral(BitVectorLiteral term) {
            return 1;
        }

        @Override
        public Integer visitIfThenElse(IfThenElse term) {
            return 1 + visit(term.condition()) + visit(term.ifTrue()) + visit(term.ifFalse());
        }

        @Override
        public Integer visitClosure(Closure term) {
            return 1 + sumVisits(term.allArguments());
        }

        @Override
        public Integer visitReflexiveClosure(ReflexiveClosure term) {
            return 1 + sumVisits(term.allArguments());
        }

        private int sumVisits(scala.collection.Iterable<? extends Term> iterable) {
            // the functional method produced unchecked warnings due to Scala/Java generics interop issues
            final int[] total = {0}; // array is a hack to get around Java lambda 'final' requirements
            iterable.foreach(term -> total[0] += visit(term));
            return total[0];
        }

    }

}
