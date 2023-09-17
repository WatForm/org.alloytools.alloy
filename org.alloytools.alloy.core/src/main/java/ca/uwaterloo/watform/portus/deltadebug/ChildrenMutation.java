package ca.uwaterloo.watform.portus.deltadebug;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

// TODO remember to recurse inside if nothing else
public final class ChildrenMutation<E extends Expr> implements Mutation {

    public static final ChildrenMutation<ExprList> AND_OR = new ChildrenMutation<>(
            ExprList.class, e -> e.op == ExprList.Op.AND || e.op == ExprList.Op.OR, e -> e.args);

    public static final ChildrenMutation<ExprBinary> BINARY = new ChildrenMutation<>(ExprBinary.class,
            e -> e.op == ExprBinary.Op.IMPLIES
                    || e.op == ExprBinary.Op.IFF
                    || e.op == ExprBinary.Op.PLUS
                    || e.op == ExprBinary.Op.MINUS
                    || e.op == ExprBinary.Op.INTERSECT
                    || e.op == ExprBinary.Op.PLUSPLUS
                    || e.op == ExprBinary.Op.IPLUS
                    || e.op == ExprBinary.Op.IMINUS
                    || e.op == ExprBinary.Op.MUL
                    || e.op == ExprBinary.Op.DIV
                    || e.op == ExprBinary.Op.REM,
            e -> Arrays.asList(e.left, e.right));

    public static final ChildrenMutation<ExprUnary> UNARY = new ChildrenMutation<>(ExprUnary.class,
            e -> e.op == ExprUnary.Op.NOT
                    || e.op == ExprUnary.Op.TRANSPOSE
                    || e.op == ExprUnary.Op.CLOSURE
                    || e.op == ExprUnary.Op.RCLOSURE,
            e -> Collections.singletonList(e.sub));

    public static final ChildrenMutation<ExprITE> ITE = new ChildrenMutation<>(ExprITE.class,
            // not the condition since that a) semantically makes no sense and b) might not match the type
            e -> Arrays.asList(e.left, e.right));

    public static final ChildrenMutation<ExprQt> QUANTIFIER = new ChildrenMutation<>(ExprQt.class,
            e -> e.op == ExprQt.Op.ALL
                    || e.op == ExprQt.Op.LONE
                    || e.op == ExprQt.Op.SOME
                    || e.op == ExprQt.Op.NO,
            e -> Collections.singletonList(e.sub));

    private final Class<E> applicableExprClass;
    private final Predicate<E> predicate;
    private final Function<E, List<? extends Expr>> childrenFunction;

    public ChildrenMutation(Class<E> applicableExprClass, Predicate<E> predicate,
                            Function<E, List<? extends Expr>> childrenFunction) {
        this.applicableExprClass = applicableExprClass;
        this.predicate = predicate;
        this.childrenFunction = childrenFunction;
    }

    public ChildrenMutation(Class<E> applicableExprClass, Function<E, List<? extends Expr>> childrenFunction) {
        this(applicableExprClass, e -> true, childrenFunction);
    }

    @Override
    public List<State> mutate(State state) {
        if (!applicableExprClass.isInstance(state.currentSubformula)) {
            return Collections.emptyList();
        }

        @SuppressWarnings("unchecked") // don't worry about multiple threads
        E currentSubformula = (E) state.currentSubformula;
        if (!predicate.test(currentSubformula)) {
            return Collections.emptyList();
        }

        List<? extends Expr> children = childrenFunction.apply(currentSubformula);

        // Replace the whole thing with one child each time, in order of appearance
        // TODO: a better order based on some heuristic? size maybe?
        return children.stream()
                .map(state::replaceCurrentSubformula)
                .collect(Collectors.toList());
    }

}
