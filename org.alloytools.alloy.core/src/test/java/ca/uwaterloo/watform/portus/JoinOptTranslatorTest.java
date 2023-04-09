package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Var;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;

import static ca.uwaterloo.watform.portus.IsSameMatcher.isSameAs;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;
import static org.mockito.hamcrest.MockitoHamcrest.argThat;

public class JoinOptTranslatorTest {

    private final Sort testSort = Sort.mkSortConst("testSort");

    private Translator translator;
    private Translator mockRoot;

    private SortPolicy mockSortPolicy;
    private TranslationContext context;

    @Before
    public void setUp() {
        mockRoot = mock(Translator.class);
        translator = new JoinOptTranslator(mockRoot);
        mockSortPolicy = mock(SortPolicy.class);
        when(mockSortPolicy.addSortsToTheory(any())).thenReturn(Theory.empty().withSort(testSort));
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class, withSettings().useConstructor(new ArrayList<>()));
        ScopeComputer mockScoper = mock(ScopeComputer.class);
        context = new TranslationContext(new PortusOptions(), mockScoper, mockSortPolicy, mockRangeAssigner);
    }

    @Test
    public void testTranslate_nonJoin() {
        // test that translating some random binary expression doesn't do anything
        assertNull(translator.translate(ExprConstant.TRUE.and(ExprConstant.FALSE), context));
    }

    @Test
    public void testTranslate_join_inapplicable() {
        // test that [[x \in e1 . e2]] doesn't get optimized when neither are variables
        ExprVar a = ExprVar.make(null, "a");
        ExprVar b = ExprVar.make(null, "b");
        assertNull(translator.translate(a.product(b).join(a.product(b)), context));
    }

    @Test
    public void testTranslate_join_left() {
        // test [[x \in v . e]] := [[(v,x) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(v, x), e))), any()))
                .thenReturn(flag);

        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), alloyV.join(e)), context));
    }

    @Test
    public void testTranslate_join_right() {
        // test [[x \in e . v]] := [[(x,v) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x, v), e))), any()))
                .thenReturn(flag);

        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), e.join(alloyV)), context));
    }

    @Test
    public void testTranslate_join_leftWithNoop() {
        // test [[x \in NOOP(v) . e]] := [[(v,x) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(v, x), e))), any()))
                .thenReturn(flag);

        Expr noop = ExprUnary.Op.NOOP.make(null, alloyV);
        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), noop.join(e)), context));
    }

    @Test
    public void testTranslate_join_rightWithNoop() {
        // test [[x \in e . NOOP(v)]] := [[(x,v) \in e]]
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x, v), e))), any()))
                .thenReturn(flag);

        Expr noop = ExprUnary.Op.NOOP.make(null, alloyV);
        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), e.join(noop)), context));
    }

    @Test
    public void testTranslate_join_leftWithLet() {
        // test [[x \in y . e]] := [[(v,x) \in e]] when y is mapped to v in a let mapping
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        ExprVar alloyY = ExprVar.make(null, "y");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));
        context.addLetMapping("y", alloyV);

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(v, x), e))), any()))
                .thenReturn(flag);

        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), alloyY.join(e)), context));
    }

    @Test
    public void testTranslate_join_rightWithLet() {
        // test [[x \in y . e]] := [[(v,x) \in e]] when y is mapped to v in a let mapping
        Sig sigA = new Sig.PrimSig("A");
        Sig sigB = new Sig.PrimSig("B");
        when(mockSortPolicy.getSort(sigA)).thenReturn(testSort);
        when(mockSortPolicy.getSort(sigB)).thenReturn(testSort);
        Expr e = sigA.product(sigB);

        ExprVar alloyV = ExprVar.make(null, "v");
        ExprVar alloyY = ExprVar.make(null, "y");
        AnnotatedVar v = Term.mkVar("v").of(testSort);
        context.addTermMapping("v", new AnnotatedTerm(v));
        context.addLetMapping("y", alloyV);

        AnnotatedVar x = Term.mkVar("x").of(testSort);
        Var flag = Term.mkVar("flag");
        when(mockRoot.translate(argThat(isSameAs(ExprElementOf.make(TermTuple.fromVars(x, v), e))), any()))
                .thenReturn(flag);

        //noinspection SuspiciousNameCombination
        assertEquals(flag, translator.translate(ExprElementOf.make(TermTuple.fromVars(x), e.join(alloyY)), context));
    }

}
