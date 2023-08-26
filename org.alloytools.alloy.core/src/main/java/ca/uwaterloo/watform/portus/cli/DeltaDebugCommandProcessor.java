package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

final class DeltaDebugCommandProcessor implements CommandProcessor {

    @Override
    public void process(Iterable<Sig> sigs, Command command, A4Options options) {
        
    }

    @Override
    public String displayName() {
        return "Delta Debugging";
    }

}
