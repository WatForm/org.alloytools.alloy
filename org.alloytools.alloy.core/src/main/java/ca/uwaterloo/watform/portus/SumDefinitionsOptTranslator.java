package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * An optimization that extracts the sum and cardinality sub-expressions into definitions.
 * This way when we expand over the sorts, only the definition call is repeated instead of the entire expression.
 */
// TODO: There's a lot of duplication between here and the relevant parts of DefaultTranslator
// TODO: Use a heuristic to decide whether to apply the opt or not based on the size of the term
final class SumDefinitionsOptTranslator extends AbstractTranslator {

    private final SortPolicy sortPolicy;
    private final NameGenerator nameGenerator;

    // If true, balance the generated addends like ((1 + 1) + (1 + 1)) + ((1 + 1) + (1 + 1)).
    // If false, just generate it left-associative: ((((((1 + 1) + 1) + 1) + 1) + 1) + 1) + 1
    private final boolean useBalancing;

    public SumDefinitionsOptTranslator(
            Translator topLevel, SortPolicy sortPolicy, NameGenerator nameGenerator, boolean useBalancing) {
        super(topLevel);
        this.sortPolicy = sortPolicy;
        this.nameGenerator = nameGenerator;
        this.useBalancing = useBalancing;
    }

    @Override
    public String name() {
        return "Sum Definitions Optimization";
    }

    @Override
    public Term translate(ExprUnary expr, TranslationContext context) {
        if (expr.op != ExprUnary.Op.CARDINALITY) return null;

        SortResolvant resolvant = sortPolicy.getMinimalExprSorts(expr.sub, context);
        if (!resolvant.isDefinite()) {
            return null; // let someone else handle it
        }
        List<Sort> sorts = resolvant.getDefiniteSorts();

        List<AnnotatedVar> vars = new ArrayList<>();
        for (int i = 0; i < expr.sub.type().arity(); i++) {
            Var var = Term.mkVar(nameGenerator.freshName("x" + i));
            vars.add(var.of(sorts.get(i)));
        }

        Expr conditionExpr = ExprElementOf.make(TermTuple.fromVars(vars), expr.sub);
        try {
            context.addFortressVars(vars); // Add only the expanded-only vars since free vars should already be in scope
            Term condition = recursivelyTranslate(conditionExpr, context);
            AnnotatedTerm conditionAnnotated = new AnnotatedTerm(condition, Sort.Bool());
            return translateSum(
                    new AnnotatedTerm(IntegerLiteral.apply(1), Sort.Int()), conditionAnnotated, vars, context);
        } finally {
            context.removeFortressVars(vars);
        }
    }

    @Override
    public Term translate(ExprQt expr, TranslationContext context) {
        if (expr.op != ExprQt.Op.SUM) return null;

        // If we need to short-circuit, let someone else handle it
        boolean isNone = expr.decls.stream()
                .map(decl -> sortPolicy.getMinimalExprSorts(decl.expr, context))
                .anyMatch(SortResolvant::isNone);
        if (isNone) {
            return null;
        }

        Pair<Pair<List<String>, List<AnnotatedVar>>, AnnotatedTerm> varsAndCond =
                PortusUtil.translateDeclList(expr.decls, context, sortPolicy, topLevelTranslator, nameGenerator);
        List<String> alloyVarNames = varsAndCond.a.a;
        List<AnnotatedVar> vars = varsAndCond.a.b;
        AnnotatedTerm condition = varsAndCond.b;

        // Process subformula - Fortress vars were added to the lexical scope in translateDeclList()
        try {
            Term subTerm = recursivelyTranslate(expr.sub, context);
            AnnotatedTerm sub = new AnnotatedTerm(subTerm, Sort.Int());
            return translateSum(sub, condition, vars, context);
        } finally {
            // Remove the vars from the lexical scope since it's done
            for (String alloyVarName : alloyVarNames) {
                context.removeMapping(alloyVarName);
            }
            context.removeFortressVars(vars);
        }
    }

    private Term translateSum(
            AnnotatedTerm sub, AnnotatedTerm condition, List<AnnotatedVar> vars, TranslationContext context) {
        // To translate "sum x: e | f", make a definition
        //   sumdef(y) := [[y \in e]] => [[f[y/x]]] else 0
        // and expand over sort(e):
        //   sumdef(_@1S) + sumdef(_@2S) + ... + sumdef(_@nS)
        // Hopefully the definition makes it more efficient!

        // We need to care about the free variables
        // Deduplicate them all and assign an arbitrary order
        Set<AnnotatedVar> allFreeVarsSet = new HashSet<>(PortusUtil.computeTermFreeVars(sub.getTerm(), context));
        allFreeVarsSet.addAll(PortusUtil.computeTermFreeVars(condition.getTerm(), context));
        vars.forEach(allFreeVarsSet::remove); // if there are any duplicates with the vars, remove them
        List<AnnotatedVar> freeVarsAnnotated = new ArrayList<>(allFreeVarsSet);
        List<Var> freeVars = freeVarsAnnotated.stream()
                .map(AnnotatedVar::variable)
                .collect(Collectors.toList());

        List<AnnotatedVar> allVars = SetOps.concatenate(vars, freeVarsAnnotated);

        // Add the definition
        String defName = nameGenerator.freshName("sum_def");
        Term body = Term.mkIfThenElse(condition.getTerm(), sub.getTerm(), IntegerLiteral.apply(0));
        FunctionDefinition definition = FunctionDefinition.mkFunctionDefinition(
                defName, allVars, Sort.Int(), body);
        context.addFunctionDefinition(definition);

        // Get all the relevant sorts
        List<Sort> sorts = new ArrayList<>();
        for (AnnotatedVar var : vars) {
            Sort sort = var.sort();
            sorts.add(sort);

            if (!sort.equals(Sort.Int())) {
                // We're expanding over the domain elements of the sort, so its scope can't be changed arbitrarily
                // in the output - mark it unchanging
                context.markSortUnchanging(sort);
            }
        }

        // Get all the addends
        List<Term> addends = new ArrayList<>();
        PortusUtil.expandOverSorts(sorts, sortPolicy, tuple -> {
            Term addend = Term.mkApp(defName, SetOps.concatenate(tuple, freeVars));
            addends.add(addend);
        });

        if (useBalancing) {
            return combineBalanced(addends);
        } else {
            return combineLeftAssociative(addends);
        }
    }

    private Term combineLeftAssociative(List<Term> addends) {
        return addends.stream().reduce(Term::mkPlus).orElse(IntegerLiteral.apply(0));
    }

    private Term combineBalanced(List<Term> addends) {
        if (addends.isEmpty()) return IntegerLiteral.apply(0);
        int length = addends.size();
        if (length == 1) return addends.get(0);

        int leftSize = (length / 2) + (length % 2); // put extra on the left
        List<Term> leftView = addends.subList(0, leftSize);
        List<Term> rightView = addends.subList(leftSize, length);

        return Term.mkPlus(combineBalanced(leftView), combineBalanced(rightView));
    }

}
