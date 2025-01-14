package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;

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

    /** Ensure we can serialize correctly. */
    private static final long serialVersionUID = 0L;

    // Print verbose output?
    public boolean verbose = false;

    // The timeout for the SMT solver in milliseconds, by default 20 minutes.
    public int timeoutMillis = 20 * 60 * 1000;

    // The directory to be used for any output files (e.g. for SMTLIB+ or MSFOL dumps).
    // By default, a temporary directory.
    public String outputDirectory = System.getProperty("java.io.tmpdir");

    // The name to be used for output files, without the file extension.
    // By default, a random filename.
    public String outputName = "tmp" + Math.abs(new Random().nextLong());

    // The name of the Fortress compiler to use according to the CompilersRegistry.
    public String fortressCompiler = "Standard";

    // The name of the Fortress solver to use according to the SolversRegistry.
    public String fortressSolver = "Z3NonIncCli";

    // Enable or disable each optimization individually.
    // Don't allow disabling the function optimization because it can affect correctness (join as integer expression).
    public boolean enableSimpleScalarOptimization = true;
    public boolean enableOneSigOptimization = true;
    public boolean enableJoinOptimization = true;
    public boolean enableMembershipPredicateOptimization = true;
    public boolean enableClosureOfScalarOptimization = true;
    public boolean enableIntsAsScalars = true;
    public boolean enableSumDefinitionsOptimization = true;
    public boolean enableExprDefnOptimization = true;
    public boolean enableFuncOptimization = true;

    public boolean enablePartitionSortPolicy = true;
    public boolean enableConstantsScopeAxiomStrategy = true; // alternative: cardinality; TODO: refactor this

    public boolean enableOrderingDefinition = true;
    public boolean enableClosureOptDefinition = true;
    public boolean enableSumBalancing = false;

    public boolean enableElementOfScalarOptimization = false;
    public boolean enableCaching = false;

    public boolean enableKodkodIntCompatibility = false;

    // Should we allow reliance on the Fortress non-exact scopes feature?
    // If true, we might generate Fortress sorts with non-exact scopes.
    // If false, we will always use a membership predicate instead and all Fortress sorts will have exact scopes.
    public boolean enableFortressNonExactScopes = false;

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
    public SortPolicy getSortPolicy(
            Iterable<Sig> sigs, Command command, ScopeComputer scoper, NameGenerator nameGenerator) {
        // For now, always use the partition sort policy
        if (enablePartitionSortPolicy) {
            return new PartitionSortPolicy(sigs, command, scoper, nameGenerator);
        } else {
            return new UnivSortPolicy(sigs, scoper);
        }
    }

}
