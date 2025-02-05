package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.util.Collections;
import java.util.Set;

/**
 * Holds global, immutable information about the model being translated.
 * TODO expand with more info (esp. ScopeComputer).
 * TODO evaluate whether to refactor to merge with AlloyProblem?
 */
public class ModelInfo {

    private final Set<String> stringConstants;

    public ModelInfo(AlloyProblem problem, ScopeComputer scoper) {
        this.stringConstants = computeStringConstants(problem, scoper);
    }

    private static Set<String> computeStringConstants(AlloyProblem problem, ScopeComputer scoper) {
        // Duplicate of the string logic in ScopeComputer.compute()...
        Set<String> stringConstants = problem.getAllStringConstants();
        int numStrings = scoper.sig2scope(Sig.STRING);
        for (int i = stringConstants.size(); i < numStrings; i++) {
            stringConstants.add("\"String" + i + "\"");
        }
        return Collections.unmodifiableSet(stringConstants);
    }

    /**
     * The set of all string constants in the model, including extra constants for when the scope of String is higher
     * than the number of referenced strings.
     */
    public Set<String> getStringConstants() {
        return stringConstants;
    }

    /**
     * The number of string constants in the model, including extra constants for when the scope of String is higher
     * than the number of referenced strings.
     */
    public int numStringConstants() {
        return stringConstants.size();
    }

}
