package ca.uwaterloo.watform.dash4whole;

import ca.uwaterloo.watform.parser.*;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import ca.uwaterloo.watform.rapidDash.RapidDashOptions;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.transform.CoreDashToElectrum;
import ca.uwaterloo.watform.transform.CoreDashToPython;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Scanner;

import static java.lang.System.exit;

public class RapidDash {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please remove any existing commands in the dash file. Only one command can be added to specify the scopes. If there is no command, the default scope 3 is used.");
        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = sc.nextLine();

        if (!actual.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
            return;
        }

        DashOptions.generateSigAxioms = false;
        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashOptions.isElectrum = false;

        Path path = Paths.get(actual);
        Path fileName = path.getFileName();
        Path directory = path.getParent();
        RapidDashOptions.outputDir = directory.toString() + '/' + fileName.toString().substring(0, fileName.toString().indexOf("."));
        RapidDashOptions.inputDir = directory + "/signature_config.json";
        DashOptions.outputDir = RapidDashOptions.outputDir + "AST";
        if (directory.toString() != null){
            DashOptions.dashModelLocation = directory.toString();
            RapidDashOptions.dashModelLocation = directory.toString();
        }

        A4Reporter rep = new A4Reporter();

        boolean parse = true;
        boolean toFile = false;

        if (parse) {

            System.out.println("Parsing Model");

            // Parse + typecheck the model
            System.out.println("=========== Parsing+Typechecking " + fileName + " =============");

            // Solve the Dash module first to get initial values
            DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashValidation.validateDashModel(dash);
            DashModule coreDash = new DashToCoreDash().transformToCoreDash(dash, fileName.toString(), "");
            DashModule alloy = DashOptions.isElectrum ? new CoreDashToElectrum().convertToElectrumAST(coreDash, "", "") : new CoreDashToAlloy().convertToAlloyAST(coreDash, "", "");
            alloy = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloy);
            String alloyString = new DashModuleToString(true).getString(alloy);
            // Change default Alloy command to "run init"
            StringBuilder alloyStringBuilder = new StringBuilder(alloyString);
            if (alloyStringBuilder.lastIndexOf("run runDefault1") > 0) {
                int index = alloyStringBuilder.lastIndexOf("run runDefault1");
                alloyStringBuilder.replace(index, "run runDefault1".length() + index, "run init");
                alloyString = alloyStringBuilder.toString();
            } else {
                alloyString += "run init";
            }
            CompModule alloyComp = CompUtil.parseEverything_fromString(rep, alloyString);

            A4Options options = new A4Options();

            options.solver = A4Options.SatSolver.SAT4J;

            A4Solution ans = null;
            for (Command command : alloyComp.getAllCommands()) { // Execute the command
                System.out.println("============ Command " + command + ": ============");
                ans = TranslateAlloyToKodkod.execute_command(rep, alloyComp.getAllReachableSigs(), command, options);
                System.out.println(ans); // If satisfiable...
            }


            // Start generating Python code
            dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            coreDash = new DashToCoreDash().transformToCoreDash(dash, fileName.toString(), "");

            DashPythonTranslation dashPythonTranslation = null;
            // Translate to our data-structure that has everything to be put into the template file
            if (ans != null && ans.satisfiable()) {
                dashPythonTranslation = CoreDashToPython.convertToPythonTranslation(coreDash, ans);
            } else {
                dashPythonTranslation = CoreDashToPython.convertToPythonTranslation(coreDash, null);
            }

            // Output to file or print to standard output
            if(toFile){
                CoreDashToPython.toFile(dashPythonTranslation);
            }else{
                CoreDashToPython.print(dashPythonTranslation);
            }
        }
        sc.close();
    }
}
