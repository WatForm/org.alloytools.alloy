package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.msfol.Sort;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.CALLS_REAL_METHODS;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.withSettings;

public class SortPolicyTest {

    private SortPolicy policy;
    private TranslationContext context;

    @Before
    public void setUp() {
        policy = mock(SortPolicy.class, CALLS_REAL_METHODS);
        RangeAssigner mockRangeAssigner = mock(RangeAssigner.class,
                withSettings().useConstructor(new ArrayList<>(), policy));
        context = new TranslationContext(new PortusOptions(), mock(ScopeComputer.class), policy, mockRangeAssigner);
    }

    @Test
    public void testGetMinimalExprSorts_true() {
        assertEquals(SortResolvant.definite(Sort.Bool()), policy.getMinimalExprSorts(ExprConstant.TRUE, context));
    }

    @Test
    public void testGetMinimalExprSorts_false() {
        assertEquals(SortResolvant.definite(Sort.Bool()), policy.getMinimalExprSorts(ExprConstant.FALSE, context));
    }

    @Test
    public void testGetMinimalExprSorts_intLiteral() {
        assertEquals(SortResolvant.definite(Sort.Int()),
                policy.getMinimalExprSorts(ExprConstant.makeNUMBER(5), context));
    }

    @Test
    public void testGetMinimalExprSorts_intSig() {
        // make it a sensible policy
        when(policy.getSort(Sig.SIGINT)).thenReturn(Sort.Int());
        assertEquals(SortResolvant.definite(Sort.Int()), policy.getMinimalExprSorts(Sig.SIGINT, context));
    }

    @Test
    public void testGetMinimalExprSorts_min() {
        assertEquals(SortResolvant.definite(Sort.Int()), policy.getMinimalExprSorts(ExprConstant.MIN, context));
    }

    @Test
    public void testGetMinimalExprSorts_max() {
        assertEquals(SortResolvant.definite(Sort.Int()), policy.getMinimalExprSorts(ExprConstant.MAX, context));
    }

    @Test
    public void testGetMinimalExprSorts_next() {
        assertEquals(SortResolvant.definite(Sort.Int(), Sort.Int()),
                policy.getMinimalExprSorts(ExprConstant.NEXT, context));
    }

    @Test
    public void testGetMinimalExprSorts_univ() {
        Sort someOtherSort = Sort.mkSortConst("SomeSort");
        when(policy.getAllSorts()).thenReturn(Arrays.asList(Sort.Int(), Sort.Bool(), someOtherSort));
        assertEquals(SortResolvant.univ(policy), policy.getMinimalExprSorts(Sig.UNIV, context));
    }

    @Test
    public void testGetMinimalExprSorts_none() {
        assertEquals(SortResolvant.NONE, policy.getMinimalExprSorts(Sig.NONE, context));
    }

    @Test
    public void testGetMinimalExprSorts_iden() {
        Sort someOtherSort = Sort.mkSortConst("SomeSort");
        when(policy.getAllSorts()).thenReturn(Arrays.asList(Sort.Int(), Sort.Bool(), someOtherSort));
        assertEquals(SortResolvant.iden(policy), policy.getMinimalExprSorts(ExprConstant.IDEN, context));
    }

    @Test
    public void testGetMinimalExprSorts_sig() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("MySort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(sig, context));
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
            assertEquals(SortResolvant.definite(Sort.Bool()), policy.getMinimalExprSorts(boolExpr, context));
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
            assertEquals(SortResolvant.definite(Sort.Int()), policy.getMinimalExprSorts(intExpr, context));
        }
    }

    @Test
    public void testGetMinimalExprSorts_union_sameSort() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort commonSort = Sort.mkSortConst("common");
        when(policy.getSort(sig1)).thenReturn(commonSort);
        when(policy.getSort(sig2)).thenReturn(commonSort);
        assertEquals(SortResolvant.definite(commonSort), policy.getMinimalExprSorts(sig1.plus(sig2), context));
    }

    @Test
    public void testGetMinimalExprSorts_union_differentSort() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertEquals(SortResolvant.definite(sort1).union(SortResolvant.definite(sort2)),
                policy.getMinimalExprSorts(sig1.plus(sig2), context));
    }

    @Test
    public void testGetMinimalExprSorts_union_leftNone() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(Sig.NONE.plus(sig), context));
    }

    @Test
    public void testGetMinimalExprSorts_union_rightNone() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(sig.plus(Sig.NONE), context));
    }

    @Test
    public void testGetMinimalExprSorts_union_leftUniv() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        when(policy.getAllSorts()).thenReturn(Arrays.asList(sort, Sort.Int(), Sort.Bool()));
        assertEquals(SortResolvant.univ(policy), policy.getMinimalExprSorts(Sig.UNIV.plus(sig), context));
    }

    @Test
    public void testGetMinimalExprSorts_union_rightUniv() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        when(policy.getAllSorts()).thenReturn(Arrays.asList(sort, Sort.Int(), Sort.Bool()));
        assertEquals(SortResolvant.univ(policy), policy.getMinimalExprSorts(sig.plus(Sig.UNIV), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_sameSort() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort commonSort = Sort.mkSortConst("common");
        when(policy.getSort(sig1)).thenReturn(commonSort);
        when(policy.getSort(sig2)).thenReturn(commonSort);
        assertEquals(SortResolvant.definite(commonSort), policy.getMinimalExprSorts(sig1.intersect(sig2), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_differentSorts() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertEquals(SortResolvant.NONE, policy.getMinimalExprSorts(sig1.intersect(sig2), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_leftUniv() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        when(policy.getAllSorts()).thenReturn(Arrays.asList(sort, Sort.Int(), Sort.Bool()));
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(sig.intersect(Sig.UNIV), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_rightUniv() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        when(policy.getAllSorts()).thenReturn(Arrays.asList(sort, Sort.Int(), Sort.Bool()));
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(Sig.UNIV.intersect(sig), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_leftNone() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertEquals(SortResolvant.NONE, policy.getMinimalExprSorts(Sig.NONE.intersect(sig), context));
    }

    @Test
    public void testGetMinimalExprSorts_intersect_rightNone() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);
        assertEquals(SortResolvant.NONE, policy.getMinimalExprSorts(sig.intersect(Sig.NONE), context));
    }

    @Test
    public void testGetMinimalExprSorts_arrow() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertEquals(SortResolvant.definite(sort1, sort2),
                policy.getMinimalExprSorts(sig1.product(sig2), context));
    }

    @Test
    public void testGetMinimalExprSorts_transpose() {
        Sig sig1 = new Sig.PrimSig("S1");
        Sig sig2 = new Sig.PrimSig("S2");
        Sort sort1 = Sort.mkSortConst("sort1");
        Sort sort2 = Sort.mkSortConst("sort2");
        when(policy.getSort(sig1)).thenReturn(sort1);
        when(policy.getSort(sig2)).thenReturn(sort2);
        assertEquals(SortResolvant.definite(sort2, sort1),
                policy.getMinimalExprSorts(sig1.product(sig2).transpose(), context));
    }

    @Test
    public void testGetMinimalExprSorts_join() {
        // the middle isn't checked
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
        assertEquals(SortResolvant.definite(sort1, sort3), policy.getMinimalExprSorts(join, context));
    }

    @Test
    public void testGetMinimalExprSorts_let() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);

        ExprVar x = ExprVar.make(null, "x");
        Expr let = ExprLet.make(null, x, sig, x);
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(let, context));
    }

    @Test
    public void testGetMinimalExprSorts_call() {
        Sig sig = new Sig.PrimSig("S");
        Sort sort = Sort.mkSortConst("sort");
        when(policy.getSort(sig)).thenReturn(sort);

        Decl x = sig.oneOf("x");
        Func func = new Func(null, null, "f", Collections.singletonList(x), sig, x.get());
        Expr call = ExprCall.make(null, null, func, Collections.singletonList(sig), -1);
        assertEquals(SortResolvant.definite(sort), policy.getMinimalExprSorts(call, context));
    }

}
