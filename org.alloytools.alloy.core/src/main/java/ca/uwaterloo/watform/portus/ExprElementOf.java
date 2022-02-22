package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.Browsable;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitReturn;
import fortress.msfol.Var;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Intermediate Expr produced during translation. Immutable.
 * Represents "(x1, ..., xn) \in e" where x1, ..., xn are Fortress Vars and
 * e is an Alloy expression. Used to pass down contextual info. See KT 4.4.
 */
// TODO: are the methods implemented correctly? They shouldn't be called...
final class ExprElementOf extends Expr {

    public final ConstList<Var> tuple;
    public final Expr sub;

    private ExprElementOf(ConstList<Var> tuple, Expr sub, JoinableList<Err> errs) {
        super(null, null, sub.ambiguous, Type.FORMULA, 0, sub.weight, errs);
        this.tuple = tuple;
        this.sub = sub;
    }

    /**
     * Construct a new ExprElementOf.
     * @param tuple The tuple that is a member of the expression.
     * @param sub The expression tuple is asserted to be a member of.
     */
    public static Expr make(ConstList<Var> tuple, Expr sub) {
        JoinableList<Err> errs = new JoinableList<>();
        if (tuple.size() != sub.type().arity()) {
            errs = errs.make(new ErrorType("Tuple size must match arity of expression."));
        }
        return new ExprElementOf(tuple, sub, errs);
    }

    /** Convenience constructor for an ExprElementOf with a singleton tuple. */
    public static Expr make(Var var, Expr sub) {
        return make(ConstList.make(1, var), sub);
    }

    @Override
    public List<? extends Browsable> getSubnodes() {
        return Collections.singletonList(sub);
    }

    @Override
    public <T> T accept(VisitReturn<T> visitor) throws Err {
        if (visitor instanceof FortressVisitReturn) {
            return ((FortressVisitReturn<T>) visitor).visit(this);
        } else {
            throw new ErrorFatal("ExprElementOf may only be visited by FortressVisitReturn");
        }
    }

    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warnings) {
        Expr sub = this.sub.resolve(this.sub.type(), warnings);
        return make(tuple, sub);
    }

    @Override
    public boolean isSame(Expr obj) {
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP) {
            obj = ((ExprUnary) obj).sub;
        }
        if (obj == this) return true;
        if (!(obj instanceof ExprElementOf)) return false;
        ExprElementOf x = (ExprElementOf) obj;
        return tuple.equals(x.tuple) && sub.isSame(x.sub);
    }

    @Override
    public int getDepth() {
        return 1 + sub.getDepth();
    }

    @Override
    public void toString(StringBuilder out, int indent) {
        for (int i = 0; i < indent; i++) {
            out.append(' ');
        }
        out.append(" (");
        out.append(tuple.stream().map(Var::toString).collect(Collectors.joining(", ")));
        out.append(") element-of ");
        if (indent < 0) {
            sub.toString(out, -1);
        } else {
            out.append("with type=").append(type()).append('\n');
            sub.toString(out, indent + 2);
        }
    }

    @Override
    public String getHTML() {
        return "<b>element-of</b> <i>" + sub.type() + "</i>";
    }

}
