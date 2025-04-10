/*
 * CLI for doing predicate abstraction. For now, it takes a .dsh file as input, parses and resolves it, and uses the populated DS to make a copy.
 */
package ca.uwaterloo.watform.dash4whole;

import java.util.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

import edu.mit.csail.sdg.alloy4.Version;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashErrors;
// import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;

public class DashPredicateAbstraction {

    public static void executeCommands(CompModule c, Integer cmdnum, A4Reporter rep) {
        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();

        List<Command> commands = c.getAllCommands();
        // this is an annoying way to convert a list to an array
        Integer i = 1;
        for (Command cmd : commands) { 
            if (i == cmdnum | cmdnum == 0) {
                System.out.println("Executing command: " + cmd);
                A4Solution ans = null;
                try {
                    ans = MainFunctions.executeCommand(cmd,c,rep, options);
                } catch (Exception e) {
                    DashUtilFcns.handleException(e);
                }
                if (ans.satisfiable()) {                  
                    if (cmd.expects == 1) 
                        System.out.println("Result: SAT (CORRECT)");
                    else if (cmd.expects == 0)
                        System.out.println("Result: SAT (INCORRECT)");
                    else
                        System.out.println("Result: SAT (nothing expected)");
                } else {
                    if (cmd.expects == 0) 
                        System.out.println("Result: UNSAT (CORRECT)");
                    else if (cmd.expects == 1)
                        System.out.println("Result: UNSAT (INCORRECT)");
                    else
                        System.out.println("Result: UNSAT (nothing expected)");
                }

            }
            i++;
        }
        if (cmdnum >= i) {
            System.err.println("Command number: " + cmdnum + " does not exist in file");
        }
   }

    public static void main(String[] args) throws Exception {

        if(args.length == 0) {
            System.out.println("Argument missing: filename");
            System.exit(0);
        }

        String inputFilename = args[args.length - 1]; 

        // default values
        String method = args[args.length - 2];
        Integer cmdnum = 0;
        Boolean translateOnly = true;
        Boolean printOnly = false;
        Boolean resolveOnly = false;

        System.out.println("Alloy/Dash Analyzer: " + Version.getShortversion() + " built " + Version.buildDate());
        DashOptions.isTraces = (method.equals("traces"));
        DashOptions.isTcmc = (method.equals("tcmc"));
        DashOptions.isElectrum = (method.equals("electrum"));

        if(!inputFilename.endsWith(".dsh")){
            int index = inputFilename.lastIndexOf('.');
            if (index > 0) {
                System.err.println("Expected a Dash file with 'dsh' extension: " + inputFilename);
                System.exit(-1);
            } else {
                inputFilename = inputFilename + ".dsh";
            }
        }

        Path f = Paths.get(inputFilename);

        if (Files.notExists(f)) {
            System.err.println(inputFilename + " : does not exist");
            return;
        }
            
        Path directory = f.toAbsolutePath().getParent();
        if (directory.toString() != null)
            DashOptions.dashModelLocation = directory.toString();

            
        System.out.println("Reading: " + inputFilename );
            
        //A4Reporter rep = new A4Reporter();

        try {
            // DashModule d = MainFunctions.parseDashFile(inputFilename, rep);
            // System.out.println("Parsed Dash file");
            // if (d == null) 
            //     DashErrors.emptyFile(inputFilename);
                
            // d = MainFunctions.resolveDash(d, rep);
            // System.out.println("Resolved Dash"); 
            A4Reporter rep = new A4Reporter();
            DashModule abs = MainFunctions.createAbstractModel(inputFilename);
            System.out.println("Abstract Dash model created.");       
            //abs = MainFunctions.resolveDash(abs, rep);
            //System.out.println("Abstract Dash model resolved."); 
            CompModule c = MainFunctions.translate(abs, rep);
            System.out.println("Translated abstract Dash to Alloy."); 
            
            String outfilename = inputFilename.substring(0,inputFilename.length()-4) + "-abstract.als";
            File out = new File(outfilename);
            if (!out.exists()) {
                out.createNewFile();
            }
            System.out.println("Creating: " + outfilename);
            FileWriter fw = new FileWriter(out.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(abs.toStringAlloy());
            bw.close();
            c = MainFunctions.parseAlloyFileAndResolveAll(outfilename, rep);
            //c = MainFunctions.resolveAlloy(c, rep);
            System.out.println("Resolved abstract Alloy."); 

        } 
        catch (Exception e) {
            DashUtilFcns.handleException(e);
        }

    }
}
