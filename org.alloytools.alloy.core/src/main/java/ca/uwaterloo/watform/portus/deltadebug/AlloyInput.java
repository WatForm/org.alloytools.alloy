package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.TableView;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;
import edu.mit.csail.sdg.translator.A4Options;

import java.io.IOException;
import java.io.UncheckedIOException;
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
            writer.write(",\n");
        }

        writer.write("}\n");
    }

    private static void writeExpr(Writer writer, Expr expr) {
        new VisitReturn<Void>() {
            private void write(String string) {
                try {
                    writer.write(string);
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }

            @Override
            public Void visit(ExprBinary x) throws Err {
                write("(");
                visitThis(x.left);
                write(") ");
                write(x.op.toString());
                write(" (");
                visitThis(x.right);
                write(")");
                return null;
            }

            @Override
            public Void visit(ExprList x) throws Err {
                // Handle AND and OR specially
                if (x.op == ExprList.Op.AND || x.op == ExprList.Op.OR) {
                    write("(");
                    for (int i = 0; i < x.args.size(); i++) {
                        if (i > 0) {
                            if (x.op == ExprList.Op.AND) {
                                write(") and (");
                            } else {
                                write(") or (");
                            }
                        }
                        visitThis(x.args.get(i));
                    }
                    write(")");
                } else {
                    write(x.op.toString());
                    write("[");
                    for (int i = 0; i < x.args.size(); i++) {
                        if (i > 0) {
                            write(", ");
                        }
                        visitThis(x.args.get(i));
                    }
                    write("]");
                }
                return null;
            }

            @Override
            public Void visit(ExprCall x) throws Err {
                write(x.fun.label);
                write("[");
                for (int i = 0; i < x.args.size(); i++) {
                    if (i > 0) {
                        write(", ");
                    }
                    visitThis(x.args.get(i));
                }
                write("]");
                return null;
            }

            @Override
            public Void visit(ExprConstant x) throws Err {
                if (x.op == ExprConstant.Op.STRING) {
                    write(x.string);
                } else if (x.op == ExprConstant.Op.NUMBER) {
                    write(Integer.toString(x.num));
                } else {
                    write(x.op.toString());
                }
                return null;
            }

            @Override
            public Void visit(ExprITE x) throws Err {
                write("(");
                visitThis(x.cond);
                write(") => (");
                visitThis(x.left);
                write(") else (");
                visitThis(x.right);
                write(")");
                return null;
            }

            @Override
            public Void visit(ExprLet x) throws Err {
                write("let ");
                visitThis(x.var);
                write(" = ");
                visitThis(x.expr);
                write(" | ");
                visitThis(x.sub);
                return null;
            }

            @Override
            public Void visit(ExprQt x) throws Err {
                // comprehensions are special
                if (x.op == ExprQt.Op.COMPREHENSION) {
                    write("{");
                } else {
                    write(x.op.toString());
                    write(" ");
                }

                for (int i = 0; i < x.decls.size(); i++) {
                    if (i > 0) {
                        write(", ");
                    }
                    Decl decl = x.decls.get(i);
                    for (int j = 0; j < decl.names.size(); j++) {
                        if (j > 0) {
                            write(", ");
                        }
                        write(decl.names.get(i).label);
                    }
                    write(": ");
                    visitThis(decl.expr);
                }

                write(" | ");
                visitThis(x.sub);

                if (x.op == ExprQt.Op.COMPREHENSION) {
                    write("}");
                }
                return null;
            }

            @Override
            public Void visit(ExprUnary x) throws Err {
                if (x.op == ExprUnary.Op.NOOP
                        || x.op == ExprUnary.Op.CAST2INT 
                        || x.op == ExprUnary.Op.CAST2SIGINT) {
                    visitThis(x.sub);
                    return null;
                }
                if (x.op == ExprUnary.Op.LONEOF) {
                    write("lone ");
                } else if (x.op == ExprUnary.Op.SOMEOF) {
                    write("some ");
                } else if (x.op == ExprUnary.Op.ONEOF) {
                    write("one ");
                } else if (x.op == ExprUnary.Op.SETOF) {
                    write("set ");
                } else if (x.op == ExprUnary.Op.EXACTLYOF) {
                    write("exactly ");
                } else {
                    write(x.op.toString());
                }
                write("(");
                visitThis(x.sub);
                write(")");
                return null;
            }

            @Override
            public Void visit(ExprVar x) throws Err {
                write(x.label);
                return null;
            }

            @Override
            public Void visit(Sig x) throws Err {
                write(x.label);
                return null;
            }

            @Override
            public Void visit(Sig.Field x) throws Err {
                write(x.label);
                return null;
            }

            @Override
            public Void visit(Func x) throws Err {
                return null;
            }

            @Override
            public Void visit(Assert x) throws Err {
                return null;
            }

            @Override
            public Void visit(Macro macro) throws Err {
                return null;
            }
        }.visitThis(expr);
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
        writer.write(Integer.toString(1 << (command.bitwidth < 0 ? 4 : command.bitwidth)));
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
