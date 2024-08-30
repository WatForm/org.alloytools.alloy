package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.ConstantDefinition;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import scala.jdk.javaapi.CollectionConverters;

import java.util.List;
import java.util.stream.Collectors;

/**
 * An optimization that factors out exprs that match a heuristic into definitions. The free variables are the parameters
 * of the definition and definitions are reused if possible.
 * Currently, this is function/predicate calls, which produces an effect somewhat like having definitions for
 * functions/predicates.
 */
class ExprDefnOptTranslator implements Translator {

    // Prevent re-entry in recursive calls.
    private Expr currentlyTranslating = null;

    // Cache for definition names.
    private final ExprCache<String> cache;

    private final Translator rootTranslator;
    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    public ExprDefnOptTranslator(Translator rootTranslator, SortPolicy sortPolicy, NameGenerator nameGenerator) {
        this.rootTranslator = rootTranslator;
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.cache = new ExprCache<>(sortPolicy);
    }

    private boolean shouldCache(Expr expr) {
        // This is a heuristic! However, this optimization matches usage patterns associated with funs/preds.
        if (expr instanceof ExprCall) return true;
        if (expr instanceof ExprElementOf) {
            ExprElementOf elementOf = (ExprElementOf) expr;
            return PortusUtil.stripPortusNoops(elementOf.sub) instanceof ExprCall;
        }
        return false;
    }

    private String generateDefinition(Expr expr, TranslationContext context) {
        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr, context);
        if (!resolvant.isDefinite() || resolvant.arity() != 1) {
            return null;
        }
        Sort sort = resolvant.getDefiniteSorts().get(0);
        Term result = rootTranslator.translate(expr, context);

        List<AnnotatedVar> freeVars = PortusUtil.computeFreeVariables(expr, context, sortPolicy);

        String name = nameGenerator.freshName("exprDefn");
        if (freeVars.isEmpty()) {
            ConstantDefinition definition = new ConstantDefinition(Term.mkVar(name).of(sort), result);
            context.addConstantDefinition(definition);
        } else {
            FunctionDefinition definition = new FunctionDefinition(
                    name,
                    CollectionConverters.asScala(freeVars).toSeq(),
                    sort,
                    result);
            context.addFunctionDefinition(definition);
        }
        return name;
    }

    private Term callDefinition(String defnName, Expr expr, TranslationContext context) {
        List<Term> freeVars = PortusUtil.computeFreeVariables(expr, context, sortPolicy).stream()
                .map(AnnotatedVar::variable)
                .collect(Collectors.toList());
        if (freeVars.isEmpty()) {
            // definition is a constant definition
            return Term.mkVar(defnName);
        } else {
            return Term.mkApp(defnName, freeVars);
        }
    }

    @Override
    public Term translate(Expr expr, TranslationContext context) {
        if (expr == currentlyTranslating || !shouldCache(expr)) return null;
        Expr oldCurrent = currentlyTranslating;
        currentlyTranslating = expr;
        try {
            String defnName = cache.get(expr, null, context);
            if (defnName == null) {
                defnName = generateDefinition(expr, context);
                if (defnName == null) {
                    System.out.println("Null generateDefinition: " + expr);
                    return null;
                }
                cache.put(expr, null, defnName, context);
            }
            return callDefinition(defnName, expr, context);
        } finally {
            currentlyTranslating = oldCurrent;
        }
    }

    @Override
    public String name() {
        return "Expr Definition Optimization";
    }

}
