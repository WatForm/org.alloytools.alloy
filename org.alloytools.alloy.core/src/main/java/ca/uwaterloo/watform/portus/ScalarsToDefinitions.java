package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Expr;
import fortress.data.NameGenerator;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Var;
import fortress.operations.TermOps;
import scala.jdk.javaapi.CollectionConverters;

import java.util.HashSet;
import java.util.Set;

final class ScalarsToDefinitions {

    /**
     * If expr is a scalar (when its free variables are filled in), return the corresponding function definition
     * and guard definition (or null if no guard definition is generated because it is trivial).
     * The free variables must be mapped in the context already.
     * Otherwise return null.
     */
    public static Pair<FunctionDefinition, FunctionDefinition> tryMakeDefinitions(
            String name, Expr expr, TranslationContext context,
            ScalarCaster scalarCaster, NameGenerator nameGenerator) {
        // cast to scalar, knowing that its free variables are filled in in the context
        Pair<AnnotatedTerm, Term> scalarResult = scalarCaster.castToScalar(expr, context);
        if (scalarResult == null) {
            // can't make a definition for it
            return null;
        }

        AnnotatedTerm scalar = scalarResult.a;
        Term guardTerm = scalarResult.b;

        // Assume the guard's free variables have the same sorts as the terms!!
        // TODO: just make the guard an AnnotatedTerm and avoid this checking
        @SuppressWarnings("unchecked")
        Set<Var> guardFreeVars = CollectionConverters.<Var>asJava(
                TermOps.wrapTerm(guardTerm).freeVars(context.getTheory().signature()));
        Set<AnnotatedVar> guardFreeAnnVars = new HashSet<>();
        for (Var var : guardFreeVars) {
            boolean any = false;
            for (AnnotatedVar scalarVar : scalar.getFreeVars()) {
                if (scalarVar.name().equals(var.name())) {
                    guardFreeAnnVars.add(scalarVar);
                    any = true;
                    break;
                }
            }
            if (!any) {
                throw new ErrorFatal(
                        "ScalarsToDefinitions: guard contains free variable that scalar doesn't! " + var.name());
            }
        }

        AnnotatedTerm guard = new AnnotatedTerm(guardTerm, Sort.Bool(), guardFreeAnnVars);

        FunctionDefinition scalarDefn = makeDefinition(nameGenerator.freshName(name), scalar);
        FunctionDefinition guardDefn;
        if (guardFreeVars.isEmpty()) {
            // HACK: Assume a constant guard must be constant-true and don't analyze it.
            // TODO: This is brittle to a constant-false guard!
            guardDefn = null;
        } else {
            guardDefn = makeDefinition(nameGenerator.freshName(name + "_guard"), guard);
        }

        return new Pair<>(scalarDefn, guardDefn);
    }

    public static FunctionDefinition makeDefinition(String name, AnnotatedTerm term) {
        return new FunctionDefinition(name,
                CollectionConverters.asScala(term.getFreeVars()).toSeq(),
                term.getSort(),
                term.getTerm());
    }

}
