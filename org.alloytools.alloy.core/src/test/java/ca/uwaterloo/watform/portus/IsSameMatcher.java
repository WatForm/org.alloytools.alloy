package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import org.hamcrest.Description;
import org.hamcrest.TypeSafeMatcher;

/**
 * A Hamcrest matcher that compares Alloy Exprs using isSame().
 */
public class IsSameMatcher extends TypeSafeMatcher<Expr> {

    private final Expr base;

    public IsSameMatcher(Expr base) {
        this.base = base;
    }

    public static IsSameMatcher isSameAs(Expr base) {
        return new IsSameMatcher(base);
    }

    @Override
    protected boolean matchesSafely(Expr item) {
        return base.isSame(item);
    }

    @Override
    public void describeTo(Description description) {
        description.appendText("same-as <");
        StringBuilder builder = new StringBuilder();
        base.toString(builder, -1);
        description.appendText(builder.toString()).appendText(">");
    }

}
