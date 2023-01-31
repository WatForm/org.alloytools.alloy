package ca.uwaterloo.watform.dash4whole;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;
// import java.util.Scanner;


import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashValidation;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.transform.CoreDashToElectrum;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class Dash {
    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {
        // System.out.println("Please specify the .dsh file path:");
        // Scanner sc = new Scanner(System.in);
        // String actual = sc.nextLine();

        if(args.length == 0) {
            System.out.println("No filename arguments given");
            System.exit(0);
        }

        for (String filename : args) {
            // TODO make it add the .dsh extension if not included
            if (!filename.endsWith(".dsh")) {
                System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
                break;
            }

            // TODO choose these at the cmd-line
            DashOptions.generateSigAxioms = false;
            DashOptions.ctlModelChecking = false;
            DashOptions.generateTraces = true;
            DashOptions.isElectrum = false;
            // sc.close();

            Path f = Paths.get(filename);

            if (Files.notExists(f)) {
                System.err.println(filename + " : does not exist");
                return;
            }
            
            

            // if (Files.notExists(path)) {
            //    System.err.println(filename + " : does not exist");
            //    return;
            //}

            // Path filename = path.getFileName();

            // QUES: what is this next part doing?
            Path directory = f.toAbsolutePath().getParent();
            DashOptions.outputDir = (directory.toString() + '/' + filename.toString().substring(0, filename.toString().indexOf(".")) + "AST");
            if (directory.toString() != null)
                DashOptions.dashModelLocation = directory.toString();

            A4Reporter rep = new A4Reporter();

            // QUES: why?
            boolean parse = true;

            if (parse) {

                System.out.println("Parsing Model");

                VizGUI viz = null;

                //Parse+typecheck the model
                System.out.println("=========== Parsing+Typechecking " + filename + " =============");

                DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, filename);
                DashValidation.validateDashModel(dash);
                DashModule coreDash = new DashToCoreDash().transformToCoreDash(dash, filename.toString(), "");
                //TODO make this a cmd-line option
                DashModule alloy = DashOptions.isElectrum ? new CoreDashToElectrum().convertToElectrumAST(coreDash, "", "") : new CoreDashToAlloy().convertToAlloyAST(coreDash, "", "");
                alloy = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloy);

                // Choose some default options for how you want to execute the
                // commands
                A4Options options = new A4Options();

                options.solver = A4Options.SatSolver.SAT4J;

                // TODO: Add an option for which command to execute (a number)
                for (Command command : alloy.getAllCommands()) { // Execute the command
                    System.out.println("============ Command " + command + ": ============");
                    A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, alloy.getAllReachableSigs(), command, options); // Print the outcome
                    System.out.println(ans); // If satisfiable...
                    if (ans.satisfiable()) { // You can query "ans" to find out the values of each set or // type. // This can be useful for debugging. //
                        // You can also write the outcome to an XML file
                        ans.writeXML("alloy_example_output.xml"); // // You can then visualize the XML file by calling this:
                        if (viz == null) {
                            viz = new VizGUI(false, "alloy_example_output.xml", null);
                        } else {
                            viz.loadXML("alloy_example_output.xml", true);
                        }
                    }
                }

            }
        }
    }
}
