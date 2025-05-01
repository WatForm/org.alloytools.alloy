package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.Sort;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * An imperfect cache for Alloy expressions.
 * Two exprs are considered equal if both:
 *  1. they are the same according to {@link PseudoAlphaEquivalence} after expanding lets
 *  2. in the current context, their free variables have the same Fortress sorts
 * This provides a one-sided guarantee: two expressions that compare equal are always alpha-equivalent, but two
 * alpha-equivalent expressions may not compare equal.
 * Additionally an extra sort can optionally be associated with each expr (e.g. as a return type).
 * Operations are O(n) since we linear search the cache keys every time.
 * TODO: We're recomputing the free variables on every call - if this is an issue, refactor.
 */
final class ExprCache<T> {

    private static final class CacheKey {

        private final Expr expr;
        private final List<AnnotatedVar> freeVars;
        private final Sort extraSort; // nullable

        private final VarMappingContext frozenContext;

        private CacheKey(Expr expr, Sort extraSort, TranslationContext context, SortPolicy sortPolicy) {
            if (expr == null) throw new NullPointerException();

            // Use this as the key to compare so that we don't get confused by lets
            // (without this otherwise e.g. with "fun f[x] { ^x }", we'd use the same aux function for all arguments x)
            this.expr = PortusUtil.expandLets(expr, context.getVarMappingContext(), sortPolicy);

            // computeFreeVariables also recurses through lets
            this.freeVars = PortusUtil.computeFreeVariables(expr, context, sortPolicy);

            this.extraSort = extraSort;
            this.frozenContext = new VarMappingContext(context.getVarMappingContext());
            this.frozenContext.dropAllLets(); // all lets have been expanded, so they're not valid for here!
        }

        // Override equals() but not hashCode() because there's no obvious way to hash an expr
        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            CacheKey cacheKey = (CacheKey) o;
            // PseudoAlphaEquivalence.test will already test the free var sorts
            return PseudoAlphaEquivalence.test(
                    expr, cacheKey.expr, freeVars, cacheKey.freeVars, frozenContext, cacheKey.frozenContext)
                    && Objects.equals(extraSort, cacheKey.extraSort);
        }

    }

    // O(n) operations because we can only use equals() and not hashCode().
    // TODO If this is a bottleneck, a linked list is probably more efficient!
    private final List<Pair<CacheKey, T>> cache = new ArrayList<>();

    private final SortPolicy sortPolicy;

    public ExprCache(SortPolicy sortPolicy) {
        this.sortPolicy = sortPolicy;
    }

    public void put(Expr expr, Sort extraSort, T value, TranslationContext context) {
        CacheKey key = new CacheKey(expr, extraSort, context, sortPolicy);
        remove(key);
        cache.add(new Pair<>(key, value));
    }

    private void remove(CacheKey key) {
        cache.removeIf(pair -> key.equals(pair.a));
    }

    // Return null if cache miss
    public T get(Expr expr, Sort extraSort, TranslationContext context) {
        CacheKey key = new CacheKey(expr, extraSort, context, sortPolicy);
        for (Pair<CacheKey, T> pair : cache) {
            if (key.equals(pair.a)) {
                return pair.b;
            }
        }
        return null;
    }

}
