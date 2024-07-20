package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;

import java.util.HashMap;
import java.util.Map;

/**
 * A cache with expr keys which is intelligent with respect to the var mapping context.
 * NOTE: Outdated and broken - part of ElementOfScalarCaster.
 */
final class ContextExprCache<T> {

    private final SortPolicy sortPolicy;

    private final Map<CacheKey, T> cache = new HashMap<>();

    public ContextExprCache(SortPolicy sortPolicy) {
        this.sortPolicy = sortPolicy;
    }

    public void put(Expr expr, VarMappingContext context, T value) {
        cache.put(new CacheKey(expr, context, sortPolicy), value);
    }

    public void put(Expr expr, TranslationContext context, T value) {
        put(expr, context.varMappingContext, value);
    }

    public T get(Expr expr, VarMappingContext context) {
        return cache.get(new CacheKey(expr, context, sortPolicy));
    }

    public T get(Expr expr, TranslationContext context) {
        return get(expr, context.varMappingContext);
    }

    /**
     * Exprs do not implement equals() and hashCode() in a useful way, so we use this wrapper to
     * serve as a HashMap key.
     */
    private static final class CacheKey {

        // Two exprs are equivalent with respect to their var mapping contexts if they expand to the
        // same thing, and are equal when free variables are interpreted with respect to the
        // term mappings in their var mapping contexts. The term mappings can't be included in the
        // expansions because they're Fortress terms and not Alloy exprs.
        // This logic is implemented in PortusUtil.areExprsEqual() and PortusUtil.exprHashCode().
        // Note: correctness assumes that there is no other relevant state in the translation context!

        private final Expr expr;
        private final VarMappingContext context;

        private CacheKey(Expr expr, VarMappingContext context, SortPolicy sortPolicy) {
            this.expr = PortusUtil.expandLets(expr, context, sortPolicy);
            this.context = context;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            CacheKey cacheKey = (CacheKey) o;
            return PortusUtil.areExprsEqual(expr, cacheKey.expr, context, cacheKey.context);
        }

        @Override
        public int hashCode() {
            return PortusUtil.exprHashCode(expr, context);
        }

    }

}
