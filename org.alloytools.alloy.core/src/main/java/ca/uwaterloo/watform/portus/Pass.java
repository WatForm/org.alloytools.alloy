package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;

/**
 * A pass over the Alloy AST.
 */
@FunctionalInterface
interface Pass {

    void performPass(Iterable<Sig> sigs, Command command, ScopeComputer scoper, TranslationContext context);

}
