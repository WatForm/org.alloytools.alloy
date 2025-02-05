package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.ScopeComputer;

import java.util.List;
import java.util.Set;

/**
 * The complete Alloy model finding problem presented to Portus.
 */
public final class AlloyProblem {

    private final List<Sig> sigs;
    private final Command command;
    private final A4Options options;

    public AlloyProblem(List<Sig> sigs, Command command, A4Options options) {
        this.sigs = sigs;
        this.command = command;
        this.options = options;
    }

    public AlloyProblem(Module world, Command command, A4Options options) {
        this(world.getAllReachableSigs(), command, options);
    }

    public List<Sig> getSigs() {
        return sigs;
    }

    public Command getCommand() {
        return command;
    }

    public Expr getFormula() {
        return command.formula;
    }

    public int getBitwidth() {
        return command.bitwidth;
    }

    public int getMaxSeq() {
        return command.maxseq;
    }

    public A4Options getOptions() {
        return options;
    }

    public PortusOptions getPortusOptions() {
        return options.portusOptions;
    }

    public Set<String> getAllStringConstants() {
        return command.getAllStringConstants(sigs);
    }

    public AlloyProblem withSigs(List<Sig> newSigs) {
        return new AlloyProblem(newSigs, command, options);
    }

    public AlloyProblem withCommand(Command newCommand) {
        return new AlloyProblem(sigs, newCommand, options);
    }

    public AlloyProblem withFormula(Expr newFormula) {
        Command newCommand = new Command(
                command.pos, command.nameExpr, command.label, command.check, command.overall, command.bitwidth,
                command.maxseq, command.minprefix, command.maxprefix, command.expects, command.scope,
                command.additionalExactScopes, command.commandKeyword, newFormula, command.parent);
        return withCommand(newCommand);
    }

    public AlloyProblem withBitwidth(int newBitwidth) {
        Command newCommand = new Command(
                command.pos, command.nameExpr, command.label, command.check, command.overall, newBitwidth,
                command.maxseq, command.minprefix, command.maxprefix, command.expects, command.scope,
                command.additionalExactScopes, command.commandKeyword, command.formula, command.parent);
        return withCommand(newCommand);
    }

    public ScopeComputer makeScopeComputer(A4Reporter reporter) {
        return ScopeComputer.compute(reporter, options, sigs, command).b;
    }

    // Should be used when you don't want reporting, e.g. for intermediate steps.
    public ScopeComputer makeScopeComputer() {
        return makeScopeComputer(A4Reporter.NOP);
    }

}
