package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.alloy4.TableView;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;

import java.io.IOException;
import java.io.Writer;
import java.util.stream.Collectors;

// TODO clean up public fields
public final class AlloyInput {

    private static final String PRETTY_PRINT_INDENT = " "; // matches Sig.explain()

    public final Module world;
    public final Command command;
    public final A4Options options;

    public AlloyInput(Module world, Command command, A4Options options) {
        this.world = world;
        this.command = command;
        this.options = options;
    }

    public AlloyInput withFormula(Expr formula) {
        Command newCommand = new Command(
                command.check, command.overall, command.bitwidth, command.maxseq,
                command.commandKeyword, formula);
        return new AlloyInput(world, newCommand, options);
    }

    public void writeAlloy(Writer writer) throws IOException {
        for (Sig sig : world.getAllReachableUserDefinedSigs()) {
            writeSig(writer, sig);
        }
        for (Func func : world.getAllFunc()) {
            if (func.label.contains("$")) {
                // The command gets exposed as a predicate for some reason, but sometimes
                // it can contain "$" which is invalid. So just don't write it.
                continue;
            }
            writeFunc(writer, func);
        }
        writeCommand(writer, command);
        writer.write('\n');
    }

    private static void writeFunc(Writer writer, Func func) throws IOException {
        // explain() writes the header for funcs, but with a unicode arrow for the return type - remove it
        writer.write(func.explain().replace("⟶", ":"));
        writer.write(" {\n");
        writer.write(PRETTY_PRINT_INDENT);
        writeExpr(writer, func.getBody());
        writer.write("\n}\n");
    }

    private static void writeSig(Writer writer, Sig sig) throws IOException {
        if (sig.builtin) {
            return;
        }

        if (sig.isAbstract != null) {
            writer.write("abstract ");
        }
        if (sig.isOne != null) {
            writer.write("one ");
        }
        if (sig.isLone != null) {
            writer.write("lone ");
        }
        if (sig.isSome != null) {
            writer.write("some ");
        }
        if (sig.isEnum != null) {
            writer.write("enum ");
        } else {
            writer.write("sig ");
        }

        writer.write(TableView.clean(sig.label));
        writer.write(' ');

        if (sig.isSubsig != null) {
            writer.write("extends ");
            Sig.PrimSig primSig = (Sig.PrimSig) sig;
            writer.write(TableView.clean(primSig.parent.label));
            writer.write(' ');
        } else if (sig.isSubset != null) {
            writer.write("in ");
            Sig.SubsetSig subsetSig = (Sig.SubsetSig) sig;
            writer.write(subsetSig.parents.stream()
                    .map(parent -> parent.label)
                    .collect(Collectors.joining(", ")));
            writer.write(' ');
        }

        writer.write("{\n");

        for (Sig.Field field : sig.getFields()) {
            writer.write(PRETTY_PRINT_INDENT);
            writer.write(field.label);
            writer.write(": ");
            writeExpr(writer, field.decl().expr);
            writer.write("\n");
        }

        writer.write("}\n");
    }

    private static void writeExpr(Writer writer, Expr expr) throws IOException {
        StringBuilder builder = new StringBuilder();
        expr.toString(builder, -1);
        writer.write(builder.toString());
    }

    private static void writeCommand(Writer writer, Command command) throws IOException {
        writer.write(command.check ? "check" : "run");
        writer.write(" { ");
        writeExpr(writer, command.formula);
        writer.write(" } for ");
        if (command.overall >= 0) {
            writer.write(Integer.toString(command.overall));
            writer.write(" but ");
        }
        for (CommandScope scope : command.scope) {
            writer.write(scope.toString());
            writer.write(", ");
        }
        writer.write(Integer.toString(command.bitwidth));
        writer.write(" int");
        if (command.maxseq >= 0) {
            writer.write(" seq ");
            writer.write(Integer.toString(command.maxseq));
        }
        if (command.expects >= 0) {
            writer.write(" expect ");
            writer.write(Integer.toString(command.expects));
        }
    }

    @Override
    public String toString() {
        return "AlloyInput{" +
                "world=" + world +
                ", command=" + command.formula +
                '}';
    }

}
