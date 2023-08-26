package ca.uwaterloo.watform.portus.cli;

import ca.uwaterloo.watform.portus.ExprElementOf;
import ca.uwaterloo.watform.portus.FortressVisitReturn;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.Macro;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.AlloySolution;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.UncheckedIOException;
import java.util.stream.Collectors;

final class CorrectnessChecker {

    public static final class Result {
        public enum Kind {
            OK("OK", false),
            KODKOD_SAT_FORTRESS_UNSAT("Fortress gives UNSAT but Kodkod gives SAT", true),
            FORTRESS_INTERPRETATION_INVALID("Fortress SAT interpretation not valid according to Kodkod", true);

            public final String description;
            public final boolean isError;

            Kind(String description, boolean isError) {
                this.description = description;
                this.isError = isError;
            }
        }

        public final Kind kind;
        public final AlloySolution fortressSolution;

        public Result(Kind kind, AlloySolution fortressSolution) {
            this.kind = kind;
            this.fortressSolution = fortressSolution;
        }
    }

    private final A4Options.SatSolver fortressSolver;
    private final A4Options.SatSolver kodkodSolver;

    public CorrectnessChecker(A4Options.SatSolver fortressSolver, A4Options.SatSolver kodkodSolver) {
        this.fortressSolver = fortressSolver;
        this.kodkodSolver = kodkodSolver;
    }

    private static A4Solution convertToKodkod(AlloySolution solution) {
        // Output to XML (in-memory) and then read back
        StringWriter stringWriter = new StringWriter();
        PrintWriter printWriter = new PrintWriter(stringWriter);
        solution.writeXML(printWriter, null, null);
        printWriter.flush();
        stringWriter.flush();

        String xml = stringWriter.toString();
        System.out.println(xml);
        try {
            return A4SolutionReader.read(null, new XMLNode(new StringReader(xml)));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * When we convert a FortressSolution to an A4Solution via XML, A4SolutionWriter makes new Field/Sig
     * objects, which means that A4Solution.eval() won't recognize them as the same as the Field/Sig
     * objects in formulas meant for the old FortressSolution. So map any such objects to their equivalent values
     * in the new solution, matching on names.
     * Hopefully this doesn't mess anything up...
     */
    private static Expr mapFormulaToNewA4Solution(Expr formula, A4Solution solution) {
        return new FortressVisitReturn<Expr>() {
            @Override
            public Expr visit(Sig sig) throws Err {
                // find the sig in the solution with the same name - hope the label is a unique enough ID...
                for (Sig solSig : solution.getAllReachableSigs()) {
                    if (solSig.label.equals(sig.label)) {
                        return solSig;
                    }
                }
                throw new ErrorFatal("Could not find A4Solution match for sig: " + sig.label);
            }

            @Override
            public Expr visit(Sig.Field field) throws Err {
                // find the field in the solution with the same name + sig, hope this is unique enough...
                for (Sig solSig : solution.getAllReachableSigs()) {
                    if (solSig.label.equals(field.sig.label)) {
                        for (Sig.Field sigField : solSig.getFields()) {
                            if (sigField.label.equals(field.label)) {
                                return sigField;
                            }
                        }
                    }
                }
                throw new ErrorFatal("Could not find A4Solution match for field: " + field);
            }

            @Override
            public Expr visit(ExprVar x) throws Err {
                // It *should* be fine to not deal with ExprVars because in formulas they don't refer to atoms directly
                return x;
            }

            @Override
            public Expr visit(ExprBinary x) throws Err {
                return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visit(ExprList x) throws Err {
                return ExprList.make(x.pos, x.closingBracket, x.op, x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()));
            }

            @Override
            public Expr visit(ExprCall x) throws Err {
                return ExprCall.make(x.pos, x.closingBracket, (Func) visitThis(x.fun), x.args.stream()
                        .map(this::visitThis)
                        .collect(Collectors.toList()), x.extraWeight);
            }

            @Override
            public Expr visit(ExprConstant x) throws Err {
                return x;
            }

            @Override
            public Expr visit(ExprITE x) throws Err {
                return ExprITE.make(x.pos, visitThis(x.cond), visitThis(x.left), visitThis(x.right));
            }

            @Override
            public Expr visit(ExprLet x) throws Err {
                return ExprLet.make(x.pos, (ExprVar) visitThis(x.var), visitThis(x.expr), visitThis(x.sub));
            }

            @Override
            public Expr visit(ExprQt x) throws Err {
                return x.op.make(x.pos, x.closingBracket, x.decls.stream()
                        .map(this::visitDecl)
                        .collect(Collectors.toList()), visitThis(x.sub));
            }

            @Override
            public Expr visit(ExprUnary x) throws Err {
                return x.op.make(x.pos, visitThis(x.sub));
            }

            @Override
            public Expr visit(Func x) throws Err {
                // TODO: this might recurse infinitely on recursive calls (but we don't support this anyways yet...)
                return new Func(x.pos, x.labelPos, x.label, x.decls.stream()
                        .map(this::visitDecl)
                        .collect(Collectors.toList()), visitThis(x.returnDecl), visitThis(x.getBody()));
            }

            private Decl visitDecl(Decl decl) {
                return new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar,
                        decl.names.stream()
                                .map(name -> (ExprHasName) visitThis(name))
                                .collect(Collectors.toList()),
                        visitThis(decl.expr));
            }

            @Override
            public Expr visit(ExprElementOf x) throws Err {
                return ExprElementOf.make(x.tuple, visitThis(x.sub));
            }

            @Override
            public Expr visit(Assert x) throws Err {
                throw new ErrorFatal("We don't support Assert in formulas!");
            }

            @Override
            public Expr visit(Macro macro) throws Err {
                throw new ErrorFatal("We don't support Macro in formulas!");
            }
        }.visitThis(formula);
    }

    public Result checkCorrectness(Iterable<Sig> sigs, Command command, A4Options options) {
        // Run through Portus and get a solution using Fortress
        AlloySolution fortressSol = fortressSolver.commandRunner().executeCommand(
                A4Reporter.NOP, sigs, command, options);

        if (!fortressSol.satisfiable()) {
            // Make sure Kodkod also thinks it's unsat
            AlloySolution kodkodSol = kodkodSolver.commandRunner().executeCommand(
                    A4Reporter.NOP, sigs, command, options);
            if (kodkodSol.satisfiable()) {
                return new Result(Result.Kind.KODKOD_SAT_FORTRESS_UNSAT, fortressSol);
            } else {
                return new Result(Result.Kind.OK, fortressSol);
            }
        }

        // Convert it to an A4Solution to validate it with Kodkod
        A4Solution kodkodSol = convertToKodkod(fortressSol);

        // The Kodkod-converted formula uses different objects for Sig/Field than the original formula (because it
        // was reconstructed from XML), so A4Solution.eval() won't recognize them as equivalent. Fix this by
        // mapping the Sig/Field objects to those in the new A4Solution.
        Expr kodkodCompatibleFormula = mapFormulaToNewA4Solution(command.formula, kodkodSol);

        // The assertion in the command needs to be valid according to Kodkod too
        // Typechecking should ensure we don't get any class cast errors here...
        boolean assertionValid = (boolean) kodkodSol.eval(kodkodCompatibleFormula);
        if (assertionValid) {
            return new Result(Result.Kind.OK, fortressSol);
        } else {
            return new Result(Result.Kind.FORTRESS_INTERPRETATION_INVALID, fortressSol);
        }
    }

}
