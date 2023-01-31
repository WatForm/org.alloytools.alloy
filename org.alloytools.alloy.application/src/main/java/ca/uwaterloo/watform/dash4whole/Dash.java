package ca.uwaterloo.watform.dash4whole;

import java.util.*;

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
        if(args.length == 0) {
            System.out.println("(-m traces|tcmc|electrum) (-c #) filename(s)");
            System.exit(0);
        }

        // simple roll-our-own argument parser
        // to avoid having to import an external package

        List<String> filelist = new ArrayList<>();

        // default values
        String method = "traces";
        Integer cmdnum = 0;

        for (int i=0; i<args.length;i++) {
            if (args[i].equals("-m")) {
                if (i+1 != args.length) {
                    method = args[i+1];
                    if (!(method.equals("traces") | method.equals("tcmc") | method.equals("electrum"))) {
                        System.err.println("-method must be traces, tcmc, or electrum");
                        System.exit(0);
                    }
                } else {
                   System.err.println("Method must be followed by traces, tcmc, or electrum");
                   System.exit(0); 
                }
                i++;
            } else if (args[i].equals("-c")) {
                if (i+1 != args.length) {
                    cmdnum = Integer.parseInt(args[i+1]);
                    if (cmdnum < 0) {
                        System.err.println("Command number must be greater than 1");
                        System.exit(0);
                    }
                } else {
                   System.err.println("-c must be followed by a number");
                   System.exit(0); 
                }
                i++;                   
            } else {
                // everything else is a file name
                filelist.add(args[i]);
            }
        }

        //TODO  these should have all false as defaults in DashOptions
        DashOptions.generateSigAxioms = false;
        DashOptions.generateTraces  = (method == "traces"); 
        //TODO this option should be renamed to tcmc
        DashOptions.ctlModelChecking = (method == "tcmc");
        DashOptions.isElectrum = (method == "electrum");    


        for (String filename : filelist) {
            // TODO make it add the .dsh extension if not included
            if (!filename.endsWith(".dsh")) {
                System.err.println("Expected a Dash file with 'dsh' extension");
                break;
            }

            Path f = Paths.get(filename);

            if (Files.notExists(f)) {
                System.err.println(filename + " : does not exist");
                return;
            }
            
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
                //TODO why are tcmc and traces not relevant here also?  either they are chosen in the options or chosen here?
                DashModule alloy = 
                    DashOptions.isElectrum ? 
                          new CoreDashToElectrum().convertToElectrumAST(coreDash, "", "") 
                        : new CoreDashToAlloy().convertToAlloyAST(coreDash, "", "");
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
