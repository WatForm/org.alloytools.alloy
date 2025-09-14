package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.*;
import kodkod.ast.Relation;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.instance.Universe;

import java.util.HashSet;
import java.util.Set;

final class CorrectnessChecker {

    public static final class Result {
        public enum Kind {
            OK("OK", false),
            KODKOD_SAT_FORTRESS_UNSAT("Fortress gives UNSAT but Kodkod gives SAT", true),
            FORTRESS_INTERPRETATION_INVALID("Fortress SAT interpretation not valid according to Kodkod", true),
            KODKOD_UNSAT_FORTRESS_SAT("Fortress gives SAT but Kodkod gives UNSAT " +
                    "(but Fortress interpretation valid or cannot be evaluated)", true),
            EXCEPTION("Exception thrown", true);

            public final String description;
            public final boolean isError;

            Kind(String description, boolean isError) {
                this.description = description;
                this.isError = isError;
            }
        }

        public final Kind kind;
        public final AlloySolution fortressSolution; // nonnull for kind != EXCEPTION
        public final Exception exception; // nonnull for kind == EXCEPTION

        public Result(Kind kind, AlloySolution fortressSolution) {
            this.kind = kind;
            this.fortressSolution = fortressSolution;
            this.exception = null;
        }

        public Result(Kind kind, Exception exception) {
            this.kind = kind;
            this.fortressSolution = null;
            this.exception = exception;
        }

        @Override
        public String toString() {
            return kind.description;
        }
    }

    public static final PortusOptions.FortressSmtSolver DEFAULT_FORTRESS_SOLVER = A4Options.SatSolver.Z3;
    public static final A4Options.SatSolver DEFAULT_KODKOD_SOLVER = A4Options.SatSolver.SAT4J;

    private final PortusOptions.FortressSmtSolver fortressSolver;
    private final A4Options.SatSolver kodkodSolver;

    public CorrectnessChecker(PortusOptions.FortressSmtSolver fortressSolver, A4Options.SatSolver kodkodSolver) {
        this.fortressSolver = fortressSolver;
        this.kodkodSolver = kodkodSolver;
    }

    public CorrectnessChecker() {
        this(DEFAULT_FORTRESS_SOLVER, DEFAULT_KODKOD_SOLVER);
    }

    private static kodkod.instance.TupleSet evalInUniverse(FortressSolution solution, Universe universe, Expr expr) {
        return solution.evaluateExpr(expr).toAlloy(solution, universe, true).debugGetKodkodTupleset();
    }

    private static A4Solution convertToKodkod(FortressSolution solution, A4Options options) {
        // Patterned after A4SolutionReader
        Set<String> atoms = new HashSet<>();
        Set<String> strings = new HashSet<>();

        // Collect all atoms and strings
        for (Sig sig : solution.getAllReachableSigs()) {
            if (sig.builtin && sig != Sig.STRING) continue;
            A4TupleSet tuples = solution.eval(sig);
            for (A4Tuple tuple : tuples) {
                String atom = tuple.atom(0);
                atoms.add(atom);
                if (sig == Sig.STRING) {
                    strings.add(atom);
                }
            }
        }
        int bitwidth = solution.getBitwidth();
        for (int i = Util.min(bitwidth); i <= Util.max(bitwidth); i++) {
            atoms.add(Integer.toString(i));
        }

        A4Solution kodkodSol = new A4Solution(
                solution.getOriginalCommand(), bitwidth, solution.getMinTrace(), solution.getMaxTrace(),
                solution.getMaxSeq(), strings, atoms, null, options, 1);
        Universe universe = kodkodSol.getUniverse();

        for (Sig sig : solution.getAllReachableSigs()) {
            if (sig.builtin) continue;
            kodkod.instance.TupleSet sigTuples = evalInUniverse(solution, universe, sig);
            Relation sigRel = kodkodSol.addRel(sig.label, sigTuples, sigTuples, false);
            kodkodSol.addSig(sig, sigRel);

            for (Sig.Field field : sig.getFields()) {
                kodkod.instance.TupleSet fieldTuples = evalInUniverse(solution, universe, field);
                Relation fieldRel = kodkodSol.addRel(sig.label + "." + field.label, fieldTuples, fieldTuples, false);
                kodkodSol.addField(field, fieldRel);
            }
        }

        kodkodSol.solve(A4Reporter.NOP, null, 0);
        return kodkodSol;
    }

    private boolean verifySolution(FortressSolution solution, Command command, A4Options options) {
        // Convert it to an A4Solution to validate it with Kodkod
        A4Solution kodkodSol = convertToKodkod(solution, options);
        return kodkodSol.evalModel(command, options);
    }

    public Result checkCorrectness(Module world, Command command, A4Options options) {
        return checkCorrectness(new PortusStatistics(), world, command, options);
    }

    public Result checkCorrectness(
            PortusStatistics statistics, Module world, Command command, A4Options options) {
        // Run through Portus and get a solution using Fortress
        try (FortressSolution fortressSol = fortressSolver.commandRunner().executeCommand(
                new StdoutA4Reporter(options.portusOptions.verbose), statistics, world, command, options)) {
            if (!fortressSol.satisfiable()) {
                // If Fortress reports UNSAT, evaluate for correctness reasons.
                statistics.onStartKodkod();
                AlloySolution kodkodSol = kodkodSolver.commandRunner().executeCommand(
                        A4Reporter.NOP, world, command, options);
                statistics.onKodkodFinished();

                // Make sure Kodkod also thinks it's unsat
                if (!fortressSol.satisfiable() && kodkodSol.satisfiable()) {
                    return new Result(Result.Kind.KODKOD_SAT_FORTRESS_UNSAT, fortressSol);
                } else {
                    return new Result(Result.Kind.OK, fortressSol);
                }
            }

            try {
                // Ensure the model is satisfied in the solution according to Fortress too.
                if (!verifySolution(fortressSol, command, options)) {
                    return new Result(Result.Kind.FORTRESS_INTERPRETATION_INVALID, fortressSol);
                }
            } catch (HigherOrderDeclException e) {
                // If the model contains higher-order quantifiers, eval will fail. In this case, just make sure that
                // Kodkod also thinks it's SAT.
                System.out.println("WARNING: Model contains higher-order quantifiers: cannot verify correctness of " +
                        "interpretation returned by Fortress!");
            }

            // For completeness, always also check that Kodkod thinks it's SAT.
            statistics.onStartKodkod();
            AlloySolution newKodkodSol = kodkodSolver.commandRunner().executeCommand(
                    A4Reporter.NOP, world, command, options);
            statistics.onKodkodFinished();

            if (newKodkodSol.satisfiable()) {
                return new Result(Result.Kind.OK, fortressSol);
            } else {
                return new Result(Result.Kind.KODKOD_UNSAT_FORTRESS_SAT, fortressSol);
            }
        } catch (Exception exception) {
            return new Result(Result.Kind.EXCEPTION, exception);
        }
    }

}
