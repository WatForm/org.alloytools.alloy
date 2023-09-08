package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

// TODO clean up public fields
public final class AlloyInput {

    public final Iterable<Sig> sigs;
    public final Command command;
    public final A4Options options;

    public AlloyInput(Iterable<Sig> sigs, Command command, A4Options options) {
        this.sigs = sigs;
        this.command = command;
        this.options = options;
    }

    @Override
    public String toString() {
        return "AlloyInput{" +
                "sigs=" + sigs +
                ", command=" + command.formula +
                '}';
    }

}
