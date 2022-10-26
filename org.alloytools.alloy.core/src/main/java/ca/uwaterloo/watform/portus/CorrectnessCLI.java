package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.AlloySolution;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;

/**
 * A correctness checker CLI for Portus.
 * Given a list of Alloy files on the command line, runs them through Portus and Fortress to generate
 * interpretations, then ensures that each interpretation is valid according to Kodkod.
 */
public final class CorrectnessCLI {

    private static final A4Options.SatSolver FORTRESS_SOLVER = A4Options.SatSolver.Z3;
    private static final A4Options.SatSolver KODKOD_SOLVER = A4Options.SatSolver.SAT4J;

    private static void help() {
        System.err.println("Usage: CorrectnessCLI <Alloy files...>");
    }

    private static A4Solution convertToKodkod(AlloySolution solution) throws IOException {
        // Output to XML (in-memory) and then read back
        StringWriter stringWriter = new StringWriter();
        PrintWriter printWriter = new PrintWriter(stringWriter);
        solution.writeXML(printWriter, null, null);
        printWriter.flush();
        stringWriter.flush();

        String xml = stringWriter.toString();
        System.out.println(xml);
        return A4SolutionReader.read(null, new XMLNode(new StringReader(xml)));
    }

    private static void processCommand(Module world, Command command, A4Options options) throws IOException {
        System.out.println("  Command: " + command.label);

        try {
            // Run through Portus and get a solution using Fortress
            AlloySolution fortressSol = FORTRESS_SOLVER.commandRunner().executeCommand(
                    A4Reporter.NOP, world.getAllReachableSigs(), command, options);

            if (!fortressSol.satisfiable()) {
                // Make sure Kodkod also thinks it's unsat
                AlloySolution kodkodSol = KODKOD_SOLVER.commandRunner().executeCommand(
                        A4Reporter.NOP, world.getAllReachableSigs(), command, options);
                if (kodkodSol.satisfiable()) {
                    System.out.println("  ERROR: Fortress gives UNSAT but Kodkod gives SAT");
                } else {
                    System.out.println("  OK");
                }
                return;
            }

            System.out.println("  Interpretation: " + fortressSol.format());

            // Convert it to an A4Solution to validate it with Kodkod
            A4Solution kodkodSol = convertToKodkod(fortressSol);

            System.out.println("  Kodkod interpretation: " + kodkodSol);

            // The assertion in the command needs to be valid according to Kodkod too
            // Typechecking should ensure we don't get any class cast errors here...
            boolean assertionValid = (boolean) kodkodSol.eval(command.formula);
            if (assertionValid) {
                System.out.println("  OK");
            } else {
                System.err.println("  ERROR: Interpretation not valid according to Kodkod! " + fortressSol.format());
            }
        } catch (Exception e) {
            System.err.println("  EXCEPTION:");
            e.printStackTrace();
        }
    }

    private static void processAlloyFile(String alloyFilename) {
        System.out.println("Processing " + alloyFilename + "...");
        try {
            Module world = CompUtil.parseEverything_fromFile(null, null, alloyFilename);
            List<Command> commands = world.getAllCommands();

            A4Options options = new A4Options();
            options.originalFilename = alloyFilename;

            for (Command command : commands) {
                processCommand(world, command, options);
            }
        } catch (Exception e) {
            System.err.println("EXCEPTION: " + e);
        }
    }

    public static void main(String[] args) {
        if (args.length == 0 || Arrays.asList(args).contains("-h")) {
            help();
            return;
        }

        for (String alloyFilename : args) {
            processAlloyFile(alloyFilename);
        }
    }

}
