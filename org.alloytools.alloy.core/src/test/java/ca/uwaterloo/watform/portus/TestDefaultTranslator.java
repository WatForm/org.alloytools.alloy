package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import org.junit.Before;
import org.junit.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasSize;
import static org.hamcrest.Matchers.is;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.Matchers.startsWith;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

public class TestDefaultTranslator {

    private Translator mock;
    private Translator translator;

    @Before
    public void setUp() {
        mock = mock(Translator.class);
        translator = new DefaultTranslator(mock);
    }

    @Test
    public void testTranslate_primSig_single() {
        Sig.PrimSig sig = new Sig.PrimSig("TestSig");
        ScopeComputer scoper = mock(ScopeComputer.class);
        when(scoper.sig2scope(sig)).thenReturn(5);
        TranslationContext context = new TranslationContext(A4Reporter.NOP, scoper);

        Term result = translator.translate(sig, context);
        assertThat(result, is(notNullValue())); // sig just returns something

        // shouldn't have any axioms to translate
        verify(mock, never()).translate(any(), any());

        // should have just one sort which bears its name and scope
        assertThat(context.getTheory().sortsJava(), hasSize(1));
        Sort sort = context.getSigSort(sig);
        assertThat(sort, is(notNullValue()));
        assertThat(sort.name(), startsWith("TestSig"));
        assertThat(context.getSortScope(sort), is(5));
    }

}
