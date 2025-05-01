package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.util.Collections;
import java.util.Set;

/**
 * Holds global, immutable information about the model being translated.
 * TODO expand with more info (esp. ScopeComputer).
 */
public class ModelInfo {

    private final Set<String> stringConstants;

    public ModelInfo(Iterable<Sig> allSigs, Command command, ScopeComputer scoper) {
        this.stringConstants = computeStringConstants(allSigs, command, scoper);
    }

    private static Set<String> computeStringConstants(Iterable<Sig> allSigs, Command command, ScopeComputer scoper) {
        // Duplicate of the string logic in ScopeComputer.compute()...
        Set<String> stringConstants = command.getAllStringConstants(allSigs);
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
