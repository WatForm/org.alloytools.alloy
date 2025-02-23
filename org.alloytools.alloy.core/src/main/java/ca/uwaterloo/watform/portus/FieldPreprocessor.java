package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.data.NameGenerator;

import java.util.ArrayList;
import java.util.List;

/**
 * Replaces each field which would be bounded by multiple sorts (before merging) with multiple fields, one per sort
 * combination, and replaces each usage of the field with a union of the new fields.
 * TODO LATER
 */
final class FieldPreprocessor implements Preprocessor {

    private final NameGenerator nameGenerator;

    public FieldPreprocessor(NameGenerator nameGenerator) {
        this.nameGenerator = nameGenerator;
    }

    @Override
    public AlloyProblem preprocess(AlloyProblem problem) {
        ScopeComputer scoper = problem.makeScopeComputer();
        ModelInfo modelInfo = new ModelInfo(problem, scoper);
        SortPolicy sortPolicy = PartitionSortPolicy.makeWithoutMergingSorts(
                new PortusStatistics(), problem, modelInfo, scoper, nameGenerator);

        // Split all fields from all sigs

        return null;
    }

    // Split field and add the results to newSig.
    // TODO must extend FunctionOptTranslator to handle (A->one B)&(X->Y) as a function
    private List<Sig.Field> splitField(
            Sig newSig, Sig.Field field, SortPolicy sortPolicy, VarMappingContext varMappingContext) {
        List<Expr> newExprs = PreprocessUtil.splitExpr(field.decl().expr, sortPolicy, varMappingContext);
        List<Sig.Field> newFields = new ArrayList<>();
        for (Expr expr : newExprs) {
            Sig.Field newField = newSig.addField(nameGenerator.freshName(field.label), expr);
            newFields.add(newField);
        }
        return newFields;
    }

}
