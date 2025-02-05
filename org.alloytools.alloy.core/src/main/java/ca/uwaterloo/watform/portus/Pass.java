package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.ScopeComputer;

/**
 * A pass over the Alloy AST.
 */
@FunctionalInterface
interface Pass {

    void performPass(AlloyProblem problem, ScopeComputer scoper, TranslationContext context);

}
