package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import fortress.msfol.Theory;

/**
 * The public API for Portus. Translate an Alloy AST to a Fortress theory, then attempt
 * to solve it using Fortress.
 */
public final class TranslateAlloyToFortress {

    public void executeCommand(
            A4Reporter reporter, Iterable<Sig> sigs, Command command, FortressOptions options) {
        Translator translator = new TranslatorManager(reporter, options);
        // TODO: might need to provide some ordering, like do sigs first
        Theory theory = translator.translate(command.formula, Theory.empty());
        // TODO: solve the theory and return something
    }

}
