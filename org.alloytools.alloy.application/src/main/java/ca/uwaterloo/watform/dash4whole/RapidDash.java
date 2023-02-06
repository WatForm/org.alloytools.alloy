package ca.uwaterloo.watform.dash4whole;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import ca.uwaterloo.watform.rapidDash.RapidDashOptions;
import ca.uwaterloo.watform.transform.CoreDashToPython;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

public class RapidDash {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = sc.nextLine();

        if (!actual.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
            return;
        }

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

            DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashModule coreDash = new DashToCoreDash().transformToCoreDash(dash, fileName.toString(), "");

            // Translate to our data-structure that has everything to be put into the template file
            DashPythonTranslation dashPythonTranslation = CoreDashToPython.convertToPythonTranslation(coreDash);

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
