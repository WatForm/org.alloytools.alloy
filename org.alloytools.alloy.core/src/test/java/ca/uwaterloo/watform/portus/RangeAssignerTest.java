package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class RangeAssignerTest {

    private ModelInfo modelInfo;
    private SortPolicy policy;
    private TranslationContext context;
    private ScopeComputer scoper;

    @Before
    public void setUp() {
        modelInfo = mock(ModelInfo.class);
        policy = mock(SortPolicy.class);
        when(policy.addSortsToTheory(any())).thenReturn(Theory.empty());
        scoper = mock(ScopeComputer.class);
        context = new TranslationContext(new PortusOptions(), scoper, policy,
                new RangeAssigner(modelInfo, new ArrayList<>(), policy, scoper));
    }

    private void assertRange(int left, int right, Pair<Integer, Integer> range) {
        assertEquals(left, (int) range.a);
        assertEquals(right, (int) range.b);
    }

    @Test
    public void testGetDomainElementRange_singleTopLevelSig() {
        // one sig in the sort with no siblings takes the whole DE range
        Sort sort = Sort.mkSortConst("sort");
        Sig sig = new Sig.PrimSig("S");
        // pass the sig to the range assigner's constructor
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Collections.singletonList(sig), policy, scoper);

        when(scoper.isExact(sig)).thenReturn(true);
        when(scoper.sig2scope(sig)).thenReturn(5);
        when(policy.getSort(sig)).thenReturn(sort);
        Pair<Integer, Integer> range = rangeAssigner.getDomainElementRange(sig);
        assertRange(1, 5, range);
    }

    @Test
    public void testGetDomainElementRange_twoTopLevelSigs() {
        // two sigs split the DE range
        Sort sort = Sort.mkSortConst("sort");
        Sig sig1 = new Sig.PrimSig("sig1");
        Sig sig2 = new Sig.PrimSig("sig2");
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Arrays.asList(sig1, sig2), policy, scoper);

        when(scoper.isExact(sig1)).thenReturn(true);
        when(scoper.isExact(sig2)).thenReturn(true);
        when(scoper.sig2scope(sig1)).thenReturn(3);
        when(scoper.sig2scope(sig2)).thenReturn(7);
        when(policy.getSort(sig1)).thenReturn(sort);
        when(policy.getSort(sig2)).thenReturn(sort);

        Pair<Integer, Integer> range1 = rangeAssigner.getDomainElementRange(sig1);
        assertRange(1, 3, range1);
        Pair<Integer, Integer> range2 = rangeAssigner.getDomainElementRange(sig2);
        assertRange(4, 10, range2);
    }

    @Test
    public void testGetDomainElementRange_parentAndChildSig() {
        // S1 extends S, they share the DE range
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig child = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Arrays.asList(parent, child), policy, scoper);

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(scoper.sig2scope(parent)).thenReturn(3);
        when(scoper.sig2scope(child)).thenReturn(3);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child)).thenReturn(sort);

        Pair<Integer, Integer> range1 = rangeAssigner.getDomainElementRange(parent);
        assertRange(1, 3, range1);
        Pair<Integer, Integer> range2 = rangeAssigner.getDomainElementRange(child);
        assertRange(1, 3, range2);
    }

    @Test
    public void testGetDomainElementRange_parentAndTwoChildrenSig() {
        // S1, S2 extends S, both children share the DE range owned wholly by parent
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig child1 = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        Sig.PrimSig child2 = new Sig.PrimSig(null, "S2", new Pos("", 0, 0), parent);
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(parent, child1, child2), policy, scoper);

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child1)).thenReturn(true);
        when(scoper.isExact(child2)).thenReturn(true);
        when(scoper.sig2scope(parent)).thenReturn(8);
        when(scoper.sig2scope(child1)).thenReturn(5);
        when(scoper.sig2scope(child2)).thenReturn(3);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child1)).thenReturn(sort);
        when(policy.getSort(child2)).thenReturn(sort);

        Pair<Integer, Integer> parentRange = rangeAssigner.getDomainElementRange(parent);
        assertRange(1, 8, parentRange);
        Pair<Integer, Integer> child1Range = rangeAssigner.getDomainElementRange(child1);
        assertRange(1, 5, child1Range);
        Pair<Integer, Integer> child2Range = rangeAssigner.getDomainElementRange(child2);
        assertRange(6, 8, child2Range);
    }

    @Test
    public void testGetDomainElementRange_twoTopLevelOneChild() {
        // top-level S, T with T1 extends T
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig topLevel = new Sig.PrimSig("S");
        Sig.PrimSig parent = new Sig.PrimSig("T");
        Sig.PrimSig child = new Sig.PrimSig(null, "T1", new Pos("", 0, 0), parent);
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(topLevel, parent, child), policy, scoper);

        when(scoper.isExact(topLevel)).thenReturn(true);
        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(scoper.sig2scope(topLevel)).thenReturn(3);
        when(scoper.sig2scope(parent)).thenReturn(8);
        when(scoper.sig2scope(child)).thenReturn(5);
        when(policy.getSort(topLevel)).thenReturn(sort);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child)).thenReturn(sort);

        Pair<Integer, Integer> topLevelRange = rangeAssigner.getDomainElementRange(topLevel);
        assertRange(1, 3, topLevelRange);
        Pair<Integer, Integer> parentRange = rangeAssigner.getDomainElementRange(parent);
        assertRange(4, 11, parentRange);
        Pair<Integer, Integer> childRange = rangeAssigner.getDomainElementRange(child);
        assertRange(4, 8, childRange);
    }

    @Test
    public void testGetDomainElementRange_nonExactWithNoChildren() {
        // for non-exact scopes, we fall back on the sum of the sizes of the children with exact scopes,
        // which results in ranges of size 0 when no such scopes exist
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Collections.singletonList(sig), policy, scoper);
        when(policy.getSort(sig)).thenReturn(sort);
        when(scoper.isExact(sig)).thenReturn(false);
        when(scoper.sig2scope(sig)).thenReturn(3);
        assertRange(1, 0, rangeAssigner.getDomainElementRange(sig));
    }

    @Test
    public void testGetDomainElementRange_childOfNonExact() {
        // an exact-scope child of a sig with a non-exact scope should bump up its domain element range to a minimum
        // size of the child's exact scope
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig child = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Arrays.asList(parent, child), policy, scoper);
        when(policy.getSort(parent)).thenReturn(sort);
        when(scoper.isExact(parent)).thenReturn(false);
        when(scoper.sig2scope(parent)).thenReturn(5);
        when(policy.getSort(child)).thenReturn(sort);
        when(scoper.isExact(child)).thenReturn(true);
        when(scoper.sig2scope(child)).thenReturn(3);
        assertRange(1, 3, rangeAssigner.getDomainElementRange(child));
        assertRange(1, 3, rangeAssigner.getDomainElementRange(parent));
    }

    @Test
    public void testGetDomainElementRange_nonExactTwoChildrenOneExactOneNonExact() {
        // test that the exact child is ignored in the domain element range calculation
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig childNonExact = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        // put the exact child later in the alphabet to ensure it would be sorted last
        Sig.PrimSig childExact = new Sig.PrimSig(null, "S2", new Pos("", 0, 0), parent);
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(parent, childExact, childNonExact), policy, scoper);
        when(policy.getSort(parent)).thenReturn(sort);
        when(scoper.isExact(parent)).thenReturn(false);
        when(scoper.sig2scope(parent)).thenReturn(4);
        when(policy.getSort(childNonExact)).thenReturn(sort);
        when(scoper.isExact(childExact)).thenReturn(false);
        when(scoper.sig2scope(childNonExact)).thenReturn(2);
        when(policy.getSort(childExact)).thenReturn(sort);
        when(scoper.isExact(childExact)).thenReturn(true);
        when(scoper.sig2scope(childExact)).thenReturn(3);
        assertRange(1, 3, rangeAssigner.getDomainElementRange(childExact));
        assertRange(1, 3, rangeAssigner.getDomainElementRange(parent));
        // don't check childNonExact because getDomainElementRange is explicitly not accurate for it
    }

    @Test
    public void testGetDomainElementRange_veryComplexHierarchy1() {
        // Given this hierarchy, where sigs marked with <= are non-exact and those with = are exact:
        //         A,<=
        //       /   \
        //     B,=  C,<=
        //           |
        //          D,=
        // ensure that the domain element ranges put B and D's ranges together and in that order
        // (due to alphabetical sorting of B and C).
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig(null, "B", new Pos("", 0, 0), sigA);
        Sig.PrimSig sigC = new Sig.PrimSig(null, "C", new Pos("", 0, 0), sigA);
        Sig.PrimSig sigD = new Sig.PrimSig(null, "D", new Pos("", 0, 0), sigC);
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(sigA, sigB, sigC, sigD), policy, scoper);
        when(policy.getSort(sigA)).thenReturn(sort);
        when(scoper.isExact(sigA)).thenReturn(false);
        when(scoper.sig2scope(sigA)).thenReturn(4);
        when(policy.getSort(sigB)).thenReturn(sort);
        when(scoper.isExact(sigB)).thenReturn(true);
        when(scoper.sig2scope(sigB)).thenReturn(2);
        when(policy.getSort(sigC)).thenReturn(sort);
        when(scoper.isExact(sigC)).thenReturn(false);
        when(scoper.sig2scope(sigC)).thenReturn(4);
        when(policy.getSort(sigD)).thenReturn(sort);
        when(scoper.isExact(sigD)).thenReturn(true);
        when(scoper.sig2scope(sigD)).thenReturn(1);
        assertRange(1, 2, rangeAssigner.getDomainElementRange(sigB));
        assertRange(3, 3, rangeAssigner.getDomainElementRange(sigD));
        assertRange(3, 3, rangeAssigner.getDomainElementRange(sigC));
        assertRange(1, 3, rangeAssigner.getDomainElementRange(sigA));
    }

    @Test
    public void testGetDomainElementRange_veryComplexHierarchy2() {
        // Given this hierarchy, where sigs marked with <= are non-exact and those with = are exact:
        //         A,<=
        //       /   \
        //     B,<=  C,=
        //     |
        //    D,=
        // ensure that the domain element ranges put D and C's ranges together and in that order
        // (due to alphabetical sorting of B and C).
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig sigA = new Sig.PrimSig("A");
        Sig.PrimSig sigB = new Sig.PrimSig(null, "B", new Pos("", 0, 0), sigA);
        Sig.PrimSig sigC = new Sig.PrimSig(null, "C", new Pos("", 0, 0), sigA);
        Sig.PrimSig sigD = new Sig.PrimSig(null, "D", new Pos("", 0, 0), sigB);
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(sigA, sigB, sigC, sigD), policy, scoper);
        when(policy.getSort(sigA)).thenReturn(sort);
        when(scoper.isExact(sigA)).thenReturn(false);
        when(scoper.sig2scope(sigA)).thenReturn(4);
        when(policy.getSort(sigB)).thenReturn(sort);
        when(scoper.isExact(sigB)).thenReturn(false);
        when(scoper.sig2scope(sigB)).thenReturn(3);
        when(policy.getSort(sigC)).thenReturn(sort);
        when(scoper.isExact(sigC)).thenReturn(true);
        when(scoper.sig2scope(sigC)).thenReturn(1);
        when(policy.getSort(sigD)).thenReturn(sort);
        when(scoper.isExact(sigD)).thenReturn(true);
        when(scoper.sig2scope(sigD)).thenReturn(2);
        assertRange(1, 2, rangeAssigner.getDomainElementRange(sigD));
        assertRange(1, 2, rangeAssigner.getDomainElementRange(sigB));
        assertRange(3, 3, rangeAssigner.getDomainElementRange(sigC));
        assertRange(1, 3, rangeAssigner.getDomainElementRange(sigA));
    }

    @Test
    public void testGetDomainElementRange_int() {
        // we don't support DE ranges for SIGINT because that's an annoying special case that will never happen
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, new ArrayList<>(), policy, scoper);
        assertNull(rangeAssigner.getDomainElementRange(Sig.SIGINT));
    }

    @Test
    public void testGetDomainElementRange_string0() {
        // no strings
        Sort stringSort = Sort.mkSortConst("String");
        when(modelInfo.getStringConstants()).thenReturn(Collections.emptySet());
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Collections.singletonList(Sig.STRING), policy, scoper);
        when(policy.getSort(Sig.STRING)).thenReturn(stringSort);
        when(scoper.isExact(any())).thenReturn(true);
        when(scoper.sig2scope(any())).thenReturn(-1);

        Pair<Integer, Integer> result = rangeAssigner.getDomainElementRange(Sig.STRING);
        assertRange(1, 0, result); // invalid range
    }

    @Test
    public void testGetDomainElementRange_string1() {
        // exactly one string
        Sort stringSort = Sort.mkSortConst("String");
        when(modelInfo.getStringConstants()).thenReturn(Collections.singleton("abc"));
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Collections.singletonList(Sig.STRING), policy, scoper);
        when(policy.getSort(Sig.STRING)).thenReturn(stringSort);
        when(scoper.isExact(any())).thenReturn(true);
        when(scoper.sig2scope(any())).thenReturn(-1);

        Pair<Integer, Integer> result = rangeAssigner.getDomainElementRange(Sig.STRING);
        assertRange(1, 1, result);
    }

    @Test
    public void testGetDomainElementRange_string2() {
        // exactly two strings
        Sort stringSort = Sort.mkSortConst("String");
        when(modelInfo.getStringConstants()).thenReturn(new HashSet<>(Arrays.asList("abc", "def")));
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Collections.singletonList(Sig.STRING), policy, scoper);
        when(policy.getSort(Sig.STRING)).thenReturn(stringSort);
        when(scoper.isExact(any())).thenReturn(true);
        when(scoper.sig2scope(any())).thenReturn(-1);

        Pair<Integer, Integer> result = rangeAssigner.getDomainElementRange(Sig.STRING);
        assertRange(1, 2, result);
    }

    @Test
    public void testGetDomainElementRange_subsetSig() {
        // we only support PrimSigs because we can't assign a definite DE range to subset sigs
        Sig parent = new Sig.PrimSig("Parent");
        Sig sig = new Sig.SubsetSig(null, "S", null, Collections.singletonList(parent));
        RangeAssigner rangeAssigner = new RangeAssigner(modelInfo, Arrays.asList(parent, sig), policy, scoper);
        assertNull(rangeAssigner.getDomainElementRange(sig));
    }

    @Test
    public void testGetDomainElementRange_siblingsIncludeBuiltins() {
        // test we don't mess up if the builtin sigs are counted as siblings like they are in reality
        // in particular, it works for strings
        Sig sig = new Sig.PrimSig("sig");
        Sort univSort = Sort.mkSortConst("univ");
        when(modelInfo.getStringConstants()).thenReturn(Collections.emptySet());
        RangeAssigner rangeAssigner = new RangeAssigner(
                modelInfo, Arrays.asList(sig, Sig.UNIV, Sig.SIGINT, Sig.SEQIDX, Sig.STRING, Sig.NONE), policy, scoper);
        when(policy.getSort(any())).thenReturn(univSort);
        when(policy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        when(policy.getSort(Sig.SEQIDX)).thenReturn(Sort.Int());
        when(scoper.isExact(any())).thenReturn(true);
        when(scoper.sig2scope(any())).thenReturn(-1); // this is returned by sig2scope when not set
        when(scoper.sig2scope(sig)).thenReturn(3);

        Pair<Integer, Integer> result = rangeAssigner.getDomainElementRange(sig);
        assertRange(1, 3, result);
    }

    @Test
    public void testAddRangeAxiom_oneElementRange() {
        Sig sig = new Sig.PrimSig("Sig");
        Sort sort = Sort.mkSortConst("Sort");
        when(policy.getSort(sig)).thenReturn(sort);

        RangeAssigner rangeAssigner = mock(RangeAssigner.class, withSettings()
                .useConstructor(mock(ModelInfo.class), Collections.singletonList(sig), policy, scoper)
                .defaultAnswer(CALLS_REAL_METHODS));
        when(rangeAssigner.getDomainElementRange(eq(sig))).thenReturn(new Pair<>(2, 2));

        Translator mockTranslator = mock(Translator.class);
        when(mockTranslator.translate(any(), any())).then(args -> {
            // should be of form "var \in sig", replace with flag(var)
            Expr expr = args.getArgument(0);
            if (!(expr instanceof ExprElementOf)) fail();
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            if (exprElementOf.tuple.size() != 1 || exprElementOf.sub != sig) fail();
            return Term.mkApp("flag", exprElementOf.tuple.getTerm(0));
        });

        rangeAssigner.addRangeAxiom(sig, mockTranslator, context);

        // Should have one axiom matching flag(@2)
        assertEquals(1, context.getTheory().axioms().size());
        Term expected = Term.mkApp("flag", Term.mkDomainElement(2, sort));
        assertEquals(expected, context.getTheory().axioms().head());
    }

    @Test
    public void testAddRangeAxiom_twoElementRange() {
        Sig sig = new Sig.PrimSig("Sig");
        Sort sort = Sort.mkSortConst("Sort");
        when(policy.getSort(sig)).thenReturn(sort);

        RangeAssigner rangeAssigner = mock(RangeAssigner.class, withSettings()
                .useConstructor(mock(ModelInfo.class), Collections.singletonList(sig), policy, scoper)
                .defaultAnswer(CALLS_REAL_METHODS));
        when(rangeAssigner.getDomainElementRange(eq(sig))).thenReturn(new Pair<>(1, 2));

        Translator mockTranslator = mock(Translator.class);
        when(mockTranslator.translate(any(), any())).then(args -> {
            // should be of form "var \in sig", replace with flag(var)
            Expr expr = args.getArgument(0);
            if (!(expr instanceof ExprElementOf)) fail();
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            if (exprElementOf.tuple.size() != 1 || exprElementOf.sub != sig) fail();
            return Term.mkApp("flag", exprElementOf.tuple.getTerm(0));
        });

        rangeAssigner.addRangeAxiom(sig, mockTranslator, context);

        // Should have one axiom matching flag(@1) & flag(@2)
        assertEquals(1, context.getTheory().axioms().size());
        Term expected = Term.mkAnd(
                Term.mkApp("flag", Term.mkDomainElement(1, sort)),
                Term.mkApp("flag", Term.mkDomainElement(2, sort)));
        assertEquals(expected, context.getTheory().axioms().head());
    }

    @Test
    public void testAddRangeAxiom_noDuplicates() {
        // Test that if we call addRangeAxiom() on the same sig twice, we don't get more axioms
        Sig sig = new Sig.PrimSig("Sig");
        Sort sort = Sort.mkSortConst("Sort");
        when(policy.getSort(sig)).thenReturn(sort);

        RangeAssigner rangeAssigner = mock(RangeAssigner.class, withSettings()
                .useConstructor(mock(ModelInfo.class), Collections.singletonList(sig), policy, scoper)
                .defaultAnswer(CALLS_REAL_METHODS));
        when(rangeAssigner.getDomainElementRange(eq(sig))).thenReturn(new Pair<>(2, 2));

        Translator mockTranslator = mock(Translator.class);
        when(mockTranslator.translate(any(), any())).then(args -> {
            // should be of form "var \in sig", replace with flag(var)
            Expr expr = args.getArgument(0);
            if (!(expr instanceof ExprElementOf)) fail();
            ExprElementOf exprElementOf = (ExprElementOf) expr;
            if (exprElementOf.tuple.size() != 1 || exprElementOf.sub != sig) fail();
            return Term.mkApp("flag", exprElementOf.tuple.getTerm(0));
        });

        rangeAssigner.addRangeAxiom(sig, mockTranslator, context);
        rangeAssigner.addRangeAxiom(sig, mockTranslator, context);

        // Should have (only) one axiom matching flag(@2)
        assertEquals(1, context.getTheory().axioms().size());
        Term expected = Term.mkApp("flag", Term.mkDomainElement(2, sort));
        assertEquals(expected, context.getTheory().axioms().head());
    }

}
