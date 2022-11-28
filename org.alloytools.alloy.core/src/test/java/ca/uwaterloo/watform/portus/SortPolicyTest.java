package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class SortPolicyTest {

    // Convenience constant so we don't have to keep casting null
    private static final Sort INDEFINITE = null;

    private SortPolicy policy;
    private TranslationContext context;
    private ScopeComputer scoper;

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class, CALLS_REAL_METHODS);
        scoper = mock(ScopeComputer.class);
        context = new TranslationContext(new FortressOptions(), scoper, policy);
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
        // pass the sig to the policy's constructor
        policy = mock(SortPolicy.class, withSettings()
                .useConstructor(Collections.singletonList(sig))
                .defaultAnswer(CALLS_REAL_METHODS));

        when(scoper.isExact(sig)).thenReturn(true);
        when(scoper.sig2scope(sig)).thenReturn(5);
        when(policy.getSort(sig)).thenReturn(sort);
        Pair<Integer, Integer> range = policy.getDomainElementRange(sig, scoper);
        assertRange(1, 5, range);
    }

    @Test
    public void testGetDomainElementRange_twoTopLevelSigs() {
        // two sigs split the DE range
        Sort sort = Sort.mkSortConst("sort");
        Sig sig1 = new Sig.PrimSig("sig1");
        Sig sig2 = new Sig.PrimSig("sig2");
        policy = mock(SortPolicy.class, withSettings()
                .useConstructor(Arrays.asList(sig1, sig2))
                .defaultAnswer(CALLS_REAL_METHODS));

        when(scoper.isExact(sig1)).thenReturn(true);
        when(scoper.isExact(sig2)).thenReturn(true);
        when(scoper.sig2scope(sig1)).thenReturn(3);
        when(scoper.sig2scope(sig2)).thenReturn(7);
        when(policy.getSort(sig1)).thenReturn(sort);
        when(policy.getSort(sig2)).thenReturn(sort);

        Pair<Integer, Integer> range1 = policy.getDomainElementRange(sig1, scoper);
        assertRange(1, 3, range1);
        Pair<Integer, Integer> range2 = policy.getDomainElementRange(sig2, scoper);
        assertRange(4, 10, range2);
    }

    @Test
    public void testGetDomainElementRange_parentAndChildSig() {
        // S1 extends S, they share the DE range
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig child = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        policy = mock(SortPolicy.class, withSettings()
                .useConstructor(Arrays.asList(parent, child))
                .defaultAnswer(CALLS_REAL_METHODS));

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(scoper.sig2scope(parent)).thenReturn(3);
        when(scoper.sig2scope(child)).thenReturn(3);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child)).thenReturn(sort);

        Pair<Integer, Integer> range1 = policy.getDomainElementRange(parent, scoper);
        assertRange(1, 3, range1);
        Pair<Integer, Integer> range2 = policy.getDomainElementRange(child, scoper);
        assertRange(1, 3, range2);
    }

    @Test
    public void testGetDomainElementRange_parentAndTwoChildrenSig() {
        // S1, S2 extends S, both children share the DE range owned wholly by parent
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig parent = new Sig.PrimSig("S");
        Sig.PrimSig child1 = new Sig.PrimSig(null, "S1", new Pos("", 0, 0), parent);
        Sig.PrimSig child2 = new Sig.PrimSig(null, "S2", new Pos("", 0, 0), parent);
        policy = mock(SortPolicy.class, withSettings()
                .useConstructor(Arrays.asList(parent, child1, child2))
                .defaultAnswer(CALLS_REAL_METHODS));

        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child1)).thenReturn(true);
        when(scoper.isExact(child2)).thenReturn(true);
        when(scoper.sig2scope(parent)).thenReturn(8);
        when(scoper.sig2scope(child1)).thenReturn(5);
        when(scoper.sig2scope(child2)).thenReturn(3);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child1)).thenReturn(sort);
        when(policy.getSort(child2)).thenReturn(sort);

        Pair<Integer, Integer> parentRange = policy.getDomainElementRange(parent, scoper);
        assertRange(1, 8, parentRange);
        Pair<Integer, Integer> child1Range = policy.getDomainElementRange(child1, scoper);
        assertRange(1, 5, child1Range);
        Pair<Integer, Integer> child2Range = policy.getDomainElementRange(child2, scoper);
        assertRange(6, 8, child2Range);
    }

    @Test
    public void testGetDomainElementRange_twoTopLevelOneChild() {
        // top-level S, T with T1 extends T
        Sort sort = Sort.mkSortConst("sort");
        Sig.PrimSig topLevel = new Sig.PrimSig("S");
        Sig.PrimSig parent = new Sig.PrimSig("T");
        Sig.PrimSig child = new Sig.PrimSig(null, "T1", new Pos("", 0, 0), parent);
        policy = mock(SortPolicy.class, withSettings()
                .useConstructor(Arrays.asList(topLevel, parent, child))
                .defaultAnswer(CALLS_REAL_METHODS));

        when(scoper.isExact(topLevel)).thenReturn(true);
        when(scoper.isExact(parent)).thenReturn(true);
        when(scoper.isExact(child)).thenReturn(true);
        when(scoper.sig2scope(topLevel)).thenReturn(3);
        when(scoper.sig2scope(parent)).thenReturn(8);
        when(scoper.sig2scope(child)).thenReturn(5);
        when(policy.getSort(topLevel)).thenReturn(sort);
        when(policy.getSort(parent)).thenReturn(sort);
        when(policy.getSort(child)).thenReturn(sort);

        Pair<Integer, Integer> topLevelRange = policy.getDomainElementRange(topLevel, scoper);
        assertRange(1, 3, topLevelRange);
        Pair<Integer, Integer> parentRange = policy.getDomainElementRange(parent, scoper);
        assertRange(4, 11, parentRange);
        Pair<Integer, Integer> childRange = policy.getDomainElementRange(child, scoper);
        assertRange(4, 8, childRange);
    }

    @Test
    public void testGetDomainElementRange_nonExact() {
        // we don't support non-exact scopes because we can't assign a definite domain element range
        Sig sig = new Sig.PrimSig("S");
        when(scoper.isExact(sig)).thenReturn(false);
        when(scoper.sig2scope(sig)).thenReturn(3);
        assertNull(policy.getDomainElementRange(sig, scoper));
    }

    @Test
    public void testGetDomainElementRange_int() {
        // we don't support DE ranges for SIGINT because that's an annoying special case that will never happen
        assertNull(policy.getDomainElementRange(Sig.SIGINT, scoper));
    }

    @Test
    public void testGetDomainElementRange_subsetSig() {
        // we only support PrimSigs because we can't assign a definite DE range to subset sigs
        Sig parent = new Sig.PrimSig("Parent");
        Sig sig = new Sig.SubsetSig(null, "S", null, Collections.singletonList(parent));
        assertNull(policy.getDomainElementRange(sig, scoper));
    }

    private void assertSorts(List<Sort> actual, Sort... expected) {
        assertArrayEquals(expected, actual.toArray());
    }

    @Test
    public void testGetMinimalExprSorts_true() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.TRUE, "", context), Sort.Bool());
    }

    @Test
    public void testGetMinimalExprSorts_false() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.FALSE, "", context), Sort.Bool());
    }

    @Test
    public void testGetMinimalExprSorts_intLiteral() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.makeNUMBER(5), "", context), Sort.Int());
    }

    @Test
    public void testGetMinimalExprSorts_intSig() {
        // make it a sensible policy
        when(policy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        assertSorts(policy.getMinimalExprSorts(Sig.SIGINT, "", context), Sort.Int());
    }

    @Test
    public void testGetMinimalExprSorts_min() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.MIN, "", context), Sort.Int());
    }

    @Test
    public void testGetMinimalExprSorts_max() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.MAX, "", context), Sort.Int());
    }

    @Test
    public void testGetMinimalExprSorts_next() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.NEXT, "", context), Sort.Int(), Sort.Int());
    }

    @Test
    public void testGetMinimalExprSorts_univ() {
        assertSorts(policy.getMinimalExprSorts(Sig.UNIV, "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalExprSorts_none() {
        assertSorts(policy.getMinimalExprSorts(Sig.NONE, "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalExprSorts_iden() {
        assertSorts(policy.getMinimalExprSorts(ExprConstant.IDEN, "", context), INDEFINITE, INDEFINITE);
    }

    @Test
    public void testGetMinimalExprSorts_sig() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("mySort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertSorts(policy.getMinimalExprSorts(sig, "", context), sort);
    }

    @Test
    public void testGetMinimalExprSorts_boolExpr() {
        // we trust typechecking, so these all get bool right away
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        when(policy.getSort(sig1)).thenReturn(Sort.mkSortConst("sort1"));
        when(policy.getSort(sig2)).thenReturn(Sort.mkSortConst("sort2"));
        Expr num1 = ExprConstant.makeNUMBER(1);
        Expr num2 = ExprConstant.makeNUMBER(2);
        Expr formula1 = num1.equal(num2);
        Expr formula2 = sig1.equal(sig2);

        List<Expr> boolExprs = Arrays.asList(
                sig1.equal(sig2),
                ExprBinary.Op.NOT_EQUALS.make(null, null, sig1, sig2),
                sig1.in(sig2),
                ExprBinary.Op.NOT_IN.make(null, null, sig1, sig2),
                ExprBinary.Op.LT.make(null, null, num1, num2),
                ExprBinary.Op.NOT_LT.make(null, null, num1, num2),
                ExprBinary.Op.LTE.make(null, null, num1, num2),
                ExprBinary.Op.NOT_LTE.make(null, null, num1, num2),
                ExprBinary.Op.GT.make(null, null, num1, num2),
                ExprBinary.Op.NOT_GT.make(null, null, num1, num2),
                ExprBinary.Op.GT.make(null, null, num1, num2),
                ExprBinary.Op.GTE.make(null, null, num1, num2),
                ExprBinary.Op.NOT_GTE.make(null, null, num1, num2),
                formula1.and(formula2),
                formula1.or(formula2),
                formula1.implies(formula2),
                formula1.iff(formula2),
                formula1.not(),
                sig1.some(),
                sig1.lone(),
                sig1.no());
        for (Expr boolExpr : boolExprs) {
            assertSorts(policy.getMinimalExprSorts(boolExpr, "", context), Sort.Bool());
        }
    }

    @Test
    public void testGetMinimalExprSorts_intExpr() {
        // we trust the typechecker so these all get int
        Expr num1 = ExprConstant.makeNUMBER(1);
        Expr num2 = ExprConstant.makeNUMBER(2);
        Sig sig = new Sig.PrimSig("S");
        when(policy.getSort(sig)).thenReturn(Sort.mkSortConst("sort"));
        List<Expr> intExprs = Arrays.asList(
                num1.iplus(num2),
                num1.iminus(num2),
                num1.mul(num2),
                num1.div(num2),
                num1.rem(num2),
                num1.shl(num2),
                num1.shr(num2),
                num1.sha(num2),
                sig.cardinality());
        for (Expr intExpr : intExprs) {
            assertSorts(policy.getMinimalExprSorts(intExpr, "", context), Sort.Int());
        }
    }

    @Test
    public void testGetMinimalSorts_union_normal() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort commonSort = Sort.mkSortConst("common");
        when(policy.getSort(sig1)).thenReturn(commonSort);
        when(policy.getSort(sig2)).thenReturn(commonSort);
        assertSorts(policy.getMinimalExprSorts(sig1.plus(sig2), "", context), commonSort);
    }

    @Test
    public void testGetMinimalSorts_union_incompatible() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertThrows(ErrorFatal.class, () -> policy.getMinimalExprSorts(sig1.plus(sig2), "expected", context));
    }

    @Test
    public void testGetMinimalSorts_union_leftIndefinite() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertSorts(policy.getMinimalExprSorts(sig.plus(Sig.UNIV), "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalSorts_union_rightIndefinite() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertSorts(policy.getMinimalExprSorts(Sig.UNIV.plus(sig), "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalSorts_union_bothIndefinite() {
        assertSorts(policy.getMinimalExprSorts(Sig.UNIV.plus(Sig.UNIV), "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalSorts_intersect_normal() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort commonSort = Sort.mkSortConst("common");
        when(policy.getSort(sig1)).thenReturn(commonSort);
        when(policy.getSort(sig2)).thenReturn(commonSort);
        assertSorts(policy.getMinimalExprSorts(sig1.intersect(sig2), "", context), commonSort);
    }

    @Test
    public void testGetMinimalSorts_intersect_incompatible() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertThrows(ErrorFatal.class, () -> policy.getMinimalExprSorts(sig1.intersect(sig2), "expected", context));
    }

    @Test
    public void testGetMinimalSorts_intersect_leftIndefinite() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertSorts(policy.getMinimalExprSorts(sig.intersect(Sig.UNIV), "", context), sort);
    }

    @Test
    public void testGetMinimalSorts_intersect_rightIndefinite() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertSorts(policy.getMinimalExprSorts(Sig.UNIV.intersect(sig), "", context), sort);
    }

    @Test
    public void testGetMinimalSorts_intersect_bothIndefinite() {
        assertSorts(policy.getMinimalExprSorts(Sig.UNIV.intersect(Sig.UNIV), "", context), INDEFINITE);
    }

    @Test
    public void testGetMinimalSorts_arrow() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertSorts(policy.getMinimalExprSorts(sig1.product(sig2), "", context), sort1, sort2);
    }

    @Test
    public void testGetMinimalSorts_transpose() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertSorts(policy.getMinimalExprSorts(sig1.product(sig2).transpose(), "", context), sort2, sort1);
    }

    @Test
    public void testGetMinimalSorts_join() {
        // trust the typechecker that the middle is okay
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sig sig3 = new Sig.PrimSig("S3");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        Sort sort3 = Sort.mkSortConst("sort3");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        when(policy.getSort(sig3)).thenReturn(sort3);
        Expr join = sig1.product(sig2).join(sig2.product(sig3));
        assertSorts(policy.getMinimalExprSorts(join, "", context), sort1, sort3);
    }

}
