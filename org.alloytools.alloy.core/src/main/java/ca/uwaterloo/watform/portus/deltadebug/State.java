package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.stream.Collectors;

// TODO clean up public fields
final class State {

    public final Module world;
    public final Expr formula;
    public final Expr currentSubformula;
    public final A4Options options;

    private final Command command;

    // first is root, last is currentSubformula
    private final Deque<Expr> pathToCurrentSubformula;

    public State(AlloyInput input) {
        this.world = input.world;
        this.formula = input.command.formula;
        this.options = input.options;
        this.command = input.command;

        // start at the root
        this.currentSubformula = this.formula;
        this.pathToCurrentSubformula = new ArrayDeque<>(Collections.singletonList(this.formula));
    }

    private State(AlloyInput input, Expr currentSubformula, Deque<Expr> pathToCurrentSubformula) {
        this.world = input.world;
        this.formula = input.command.formula;
        this.options = input.options;
        this.command = input.command;

        this.currentSubformula = currentSubformula;
        this.pathToCurrentSubformula = pathToCurrentSubformula;
    }

    public AlloyInput toInput() {
        Command newCommand = new Command(
                command.check, command.overall, command.bitwidth,
                command.maxseq, command.commandKeyword, formula);
        return new AlloyInput(world, newCommand, options);
    }

    /** Get the states created by moving the current subformula to our current subformula's children. */
    public List<State> getChildren() {
        return ASTUtil.getChildren(currentSubformula).stream()
                .map(childExpr -> {
                    Deque<Expr> newPathToCurrentSubformula = new ArrayDeque<>(pathToCurrentSubformula);
                    newPathToCurrentSubformula.addLast(childExpr);
                    return new State(toInput(), childExpr, newPathToCurrentSubformula);
                })
                .collect(Collectors.toList());
    }

    public State replaceCurrentSubformula(Expr newSubformula) {
        Deque<Expr> pathToNewSubformula = new ArrayDeque<>(pathToCurrentSubformula);
        replaceSubformula(pathToNewSubformula, newSubformula);
        Expr newRoot = pathToNewSubformula.peekFirst();
        return new State(toInput().withFormula(newRoot), newSubformula, pathToNewSubformula);
    }

    private static void replaceSubformula(Deque<Expr> pathToSubformula, Expr newSubformula) {
        // because Java has no pointers, we have to go through all the parents...
        if (pathToSubformula.isEmpty()) {
            throw new IllegalArgumentException("pathToSubformula must contain at least one element (first is root)");
        }
        if (pathToSubformula.size() == 1) {
            // easy: replace the whole thing
            pathToSubformula.remove();
            pathToSubformula.add(newSubformula);
            return;
        }

        // replace it in the children
        Expr oldRoot = pathToSubformula.removeFirst();
        Expr oldRootSubformula = pathToSubformula.peekFirst();
        replaceSubformula(pathToSubformula, newSubformula);
        Expr newRootSubformula = pathToSubformula.peekFirst();
        Expr newRoot = ASTUtil.replaceChild(oldRoot, oldRootSubformula, newRootSubformula);
        pathToSubformula.addFirst(newRoot);
    }

}
