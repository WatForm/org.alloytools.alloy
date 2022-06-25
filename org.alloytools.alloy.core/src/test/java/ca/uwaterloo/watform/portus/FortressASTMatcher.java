package ca.uwaterloo.watform.portus;

import fortress.msfol.IntegerLiteral;
import fortress.msfol.Term;
import fortress.operations.DeBruijnConverter;
import org.hamcrest.Description;
import org.hamcrest.TypeSafeMatcher;

/**
 * A Hamcrest matcher that wraps testing alpha-equivalence between Fortress terms.
 */
public class FortressASTMatcher extends TypeSafeMatcher<Term> {

    // Custom DeBruijnConverter to include integer literals
    private static final DeBruijnConverter DE_BRUIJN_CONVERTER = new DeBruijnConverter() {
        private final DeBruijnVisitor visitor = new DeBruijnVisitor() {
            // This method is necessary for Scala interop, otherwise Java complains about generics
            @Override
            public Term visit(Term term) {
                return term.accept(this);
            }

            @Override
            public Term visitIntegerLiteral(IntegerLiteral literal) {
                return literal;
            }
        };

        @Override
        public Term convert(Term term) {
            //noinspection RedundantCast - Java thinks visit() returns Object for some reason
            return (Term) visitor.visit(term);
        }
    };

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
        return DE_BRUIJN_CONVERTER.convert(base).equals(DE_BRUIJN_CONVERTER.convert(term));
    }

    @Override
    public void describeTo(Description description) {
        description.appendText("alpha-equivalent term to ").appendValue(base);
    }

}
