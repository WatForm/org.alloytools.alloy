package ca.uwaterloo.watform.dash4whole;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class CorrectnessTesting {

    private static List<File> getDashModels(String directoryName) {
        List<File> files = new ArrayList<File>();
        File directory = new File(directoryName);

        // Get all files from a directory.
        File[] fList = directory.listFiles();
        if (fList != null)
            for (File file : fList) {
                if (file.isFile() && file.getName().endsWith(".dsh")) {
                    files.add(file);
                } else if (file.isDirectory()) {
                    files.addAll(getDashModels(file.getAbsolutePath()));
                }
            }

        return files;
    }

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {
        File dirFile = new File("");
        File parentPath = dirFile.getAbsoluteFile().getParentFile();

        String dirName = parentPath.getAbsolutePath() + "\\dash-testing\\RegressionTesting";
        List<File> listOfFiles = getDashModels(dirName);
        DashOptions.generateSigAxioms = false;

        A4Reporter rep = new A4Reporter();
        // Choose some default options for how you want to execute the
        // commands
        A4Options options = new A4Options();

        options.solver = A4Options.SatSolver.SAT4J;

        for (File file : listOfFiles) {
            DashOptions.dashModelLocation = file.getParentFile().getAbsolutePath();
            DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, file.getAbsolutePath());
            DashModule coreDash = DashToCoreDash.transformToCoreDash(dash);
            DashModule alloy = CoreDashToAlloy.convertToAlloyAST(coreDash);
            alloy = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloy);

            for (Command command : alloy.getAllCommands()) {
                A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, alloy.getAllReachableSigs(), command, options);

                if (command.expects == 1 && !ans.satisfiable()) {
                    System.out.println("Warning! One counterexample or instance was expected by: " + command + " in " + file.getName() + " but there was no solution or counterexample found.");
                }
                if (command.expects == 0 && ans.satisfiable()) {
                    System.out.println("Warning! No counterexamples or instances were expected by: " + command + " in " + file.getName() + " but there was an instance or counterexample found.");
                }
            }
        }
    }
}
