package ca.uwaterloo.watform.dash4whole;


import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashOptions;
import edu.mit.csail.sdg.alloy4.A4Reporter;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

public class RapidDash {
    /**
     * RapidDash cli
     */
    public static void main(String args[]) throws Exception {
        // Parse args.
        if(args.length == 0) {
            System.out.println("Arguments: filename");
            System.out.println("expects a .dsh file");
            System.exit(0);
        } else if (args.length > 1) {
            System.out.println("Two many arguments given!");
            System.out.println("Arguments: filename");
            System.out.println("expects a .dsh file");
            System.exit(1);
        }

        String filename = args[0];
        // Args validation.
        if (!filename.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with '.dsh' extension");
            System.exit(1);
        }

        Path f = Paths.get(filename);

        if (Files.notExists(f)) {
            System.err.println(filename + " : does not exist");
            return;
        }

        Path directory = f.toAbsolutePath().getParent();
        if (directory.toString() != null)
            DashOptions.dashModelLocation = directory.toString();


        System.out.println("Reading: " + filename );

        A4Reporter rep = new A4Reporter();

        try {
            // Resolve Dash
            DashModule d = MainFunctions.parseDashFile(filename, rep);
            System.out.println("Parsed Dash file");
            if (d == null) DashErrors.emptyFile(filename);
            d = MainFunctions.resolveDash(d, rep);
            System.out.println("Resolved Dash");
            // TODO: Solve the Dash module to get initial values


        } catch (Exception e) {
            DashUtilFcns.handleException(e);
        }

    }
}