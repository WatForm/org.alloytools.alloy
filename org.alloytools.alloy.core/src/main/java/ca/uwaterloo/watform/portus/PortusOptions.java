package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.CommandRunner;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.io.File;
import java.io.Serializable;
import java.util.Random;

/**
 * All the Portus-specific options configurable by the user. Immutable.
 */
public final class PortusOptions implements Serializable {

    // File extensions used by some outputting solvers.
    public static final String SMTLIBPLUS_EXTENSION = ".smttc";
    public static final String MSFOL_EXTENSION = ".msfol";

    /**
     * A {@link SatSolver} that uses Fortress as its {@link CommandRunner}.
     * Actually an SMT solver, not a SAT solver.
     */
    public static final class FortressSmtSolver extends SatSolver implements Serializable {

        /** Ensure we can serialize correctly. */
        private static final long serialVersionUID = 0L;

        // TODO: I'd prefer this to be private...
        public FortressSmtSolver(String id, String toString) {
            // No Fortress solver is an external command and we always want to add to the solver list,
            // so pass null for the external command and options and true for whether to add.
            super(id, toString, null, null, true);
        }

        @Override
        public CommandRunner commandRunner() {
            return new TranslateAlloyToFortress();
        }

        /**
         * Get a command runner that additionally measures statistics.
         */
        public CommandRunner commandRunnerWithStatistics(PortusStatistics statistics) {
            return new TranslateAlloyToFortress(statistics);
        }

    }

    /** Ensure we can serialize correctly. */
    private static final long serialVersionUID = 0L;

    // The timeout for the SMT solver in milliseconds, by default 20 minutes.
    public int timeoutMillis = 20 * 60 * 1000;

    // The directory to be used for any output files (e.g. for SMTLIB+ or MSFOL dumps).
    // By default, a temporary directory.
    public String outputDirectory = System.getProperty("java.io.tmpdir");

    // The name to be used for output files, without the file extension.
    // By default, a random filename.
    public String outputName = "tmp" + Math.abs(new Random().nextLong());

    // Enable or disable each optimization individually.
    // Don't allow disabling the function optimization because it can affect correctness (join as integer expression).
    public boolean enableSimpleScalarOptimization = true;
    public boolean enableOneSigOptimization = true;
    public boolean enableJoinOptimization = true;
    public boolean enableOrderingModuleOptimization = true;
    public boolean enableMembershipPredicateOptimization = true;
    public boolean enablePartitionSortPolicy = true;
    public boolean enableConstantsScopeAxiomStrategy = true; // alternative: cardinality; TODO: refactor this
    public boolean enableElementOfScalarOptimization = false;
    public boolean enableCaching = false;

    // Create a PortusOptions specifying options.
    public PortusOptions(String outputDirectory, String outputName) {
        this.outputDirectory = outputDirectory;
        this.outputName = outputName;
    }

    // Create a PortusOptions with the default options.
    public PortusOptions() {}

    /** Create a file with the given extension with parameters specified in the options. */
    public File createOutputFile(String extension) {
        return new File(outputDirectory, outputName + extension);
    }

    /** Which sort policy should we use to translate? */
    public SortPolicy getSortPolicy(Iterable<Sig> sigs, Command command, ScopeComputer scoper) {
        // For now, always use the partition sort policy
        if (enablePartitionSortPolicy) {
            return new PartitionSortPolicy(sigs, command, scoper);
        } else {
            return new UnivSortPolicy(sigs, scoper);
        }
    }

}
