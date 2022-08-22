package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class SortPolicyTest {

    // Convenience constant so we don't have to keep casting null
    private static final Sort INDEFINITE = null;

    private SortPolicy policy;
    private TranslationContext context;

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class, CALLS_REAL_METHODS);
        context = new TranslationContext(new FortressOptions(), mock(ScopeComputer.class), policy);
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
    public void testGetMiniimalSorts_intersect_normal() {
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
