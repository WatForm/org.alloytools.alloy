package ca.uwaterloo.watform.portus;

import fortress.msfol.Term;
import fortress.operations.TermOps;
import org.hamcrest.Description;
import org.hamcrest.TypeSafeMatcher;

/**
 * A Hamcrest matcher that wraps testing alpha-equivalence between Fortress terms.
 */
public class FortressASTMatcher extends TypeSafeMatcher<Term> {

    // The term to compare against.
    private final Term base;

    public FortressASTMatcher(Term base) {
        this.base = base;
    }

    public static FortressASTMatcher isAlphaEquivalentTerm(Term base) {
        return new FortressASTMatcher(base);
    }

    @Override
    protected boolean matchesSafely(Term term) {
        return TermOps.wrapTerm(base).alphaEquivalent(term);
    }

    @Override
    public void describeTo(Description description) {
        description.appendText("alpha-equivalent term to ").appendValue(base);
    }

}
