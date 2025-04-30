package ca.uwaterloo.watform.portus;

import fortress.data.NameGenerator;
import fortress.msfol.*;
import fortress.operations.AuxSubstituter;
import fortress.operations.Substituter;
import scala.jdk.javaapi.CollectionConverters;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Represents the translation result of either a first or second order quantifier.
 * Basically a tagged union between an AnnotatedVar and a FuncDecl.
 * TODO rename
 */
final class DeclResult {

    private final AnnotatedVar firstOrderDecl;
    private final FuncDecl secondOrderDecl;

    private DeclResult(AnnotatedVar firstOrderDecl) {
        this.firstOrderDecl = firstOrderDecl;
        this.secondOrderDecl = null;
    }

    private DeclResult(FuncDecl secondOrderDecl) {
        this.firstOrderDecl = null;
        this.secondOrderDecl = secondOrderDecl;
    }

    public static DeclResult makeFirstOrder(AnnotatedVar firstOrderDecl) {
        return new DeclResult(firstOrderDecl);
    }

    public static DeclResult makeSecondOrder(FuncDecl secondOrderDecl) {
        return new DeclResult(secondOrderDecl);
    }

    public static List<DeclResult> makeFirstOrder(List<AnnotatedVar> firstOrderDecls) {
        return firstOrderDecls.stream().map(DeclResult::makeFirstOrder).collect(Collectors.toList());
    }

    public boolean isFirstOrder() {
        return firstOrderDecl != null;
    }

    public boolean isSecondOrder() {
        return secondOrderDecl != null;
    }

    public AnnotatedVar getFirstOrderDecl() {
        if (!isFirstOrder()) {
            throw new IllegalStateException("Cannot get first-order decl of a non-first-order DeclResult!");
        }
        return firstOrderDecl;
    }

    public FuncDecl getSecondOrderDecl() {
        if (!isSecondOrder()) {
            throw new IllegalStateException("Cannot get second-order decl of a non-second-order DeclResult!");
        }
        return secondOrderDecl;
    }

    public Term makeForall(Term body) {
        if (isFirstOrder()) {
            return Term.mkForall(getFirstOrderDecl(), body);
        } else {
            return Forall2ndOrder.apply(getSecondOrderDecl(), body);
        }
    }

    public Term makeExists(Term body) {
        if (isFirstOrder()) {
            return Term.mkExists(getFirstOrderDecl(), body);
        } else {
            return Exists2ndOrder.apply(getSecondOrderDecl(), body);
        }
    }

    public static Term makeForall(List<DeclResult> declResults, Term body) {
        Term result = body;
        for (int i = declResults.size() - 1; i >= 0; i--) {
            result = declResults.get(i).makeForall(result);
        }
        return result;
    }

    public static Term makeExists(List<DeclResult> declResults, Term body) {
        Term result = body;
        for (int i = declResults.size() - 1; i >= 0; i--) {
            result = declResults.get(i).makeExists(result);
        }
        return result;
    }

    public void addMapping(String alloyVarName, VarMappingContext varMappingContext) {
        if (isFirstOrder()) {
            varMappingContext.addTermMapping(alloyVarName, new AnnotatedTerm(getFirstOrderDecl()));
        } else {
            varMappingContext.addFuncMapping(alloyVarName, getSecondOrderDecl());
        }
    }

    public DeclResult prime(NameGenerator nameGenerator) {
        if (isFirstOrder()) {
            AnnotatedVar var = getFirstOrderDecl();
            AnnotatedVar primed = Term.mkVar(nameGenerator.freshName(var.variable().name() + "_prime")).of(var.sort());
            return makeFirstOrder(primed);
        } else {
            FuncDecl func = getSecondOrderDecl();
            //noinspection unchecked
            FuncDecl primed = FuncDecl.mkFuncDecl(nameGenerator.freshName(func.name() + "_prime"),
                    CollectionConverters.<Sort> asJava(func.argSorts()), func.resultSort());
            return makeSecondOrder(primed);
        }
    }

    public Term substitute(DeclResult other, Term term) {
        // TODO unify with PortusUtil.substitute
        if (isFirstOrder() != other.isFirstOrder()) {
            throw new IllegalArgumentException("Cannot substitute first-order for second-order or vice versa");
        }
        if (isFirstOrder()) {
            NameGenerator nameGenerator = new SanitizingNameGenerator();
            Var from = getFirstOrderDecl().variable();
            Var to = other.getFirstOrderDecl().variable();
            return Substituter.apply(from, to, term, nameGenerator);
        } else {
            FuncDecl from = getSecondOrderDecl();
            FuncDecl to = other.getSecondOrderDecl();
            return AuxSubstituter.renameApplications(term, from.name(), to.name());
        }
    }

    public Term makeEqual(DeclResult other, NameGenerator nameGenerator) {
        if (isFirstOrder() != other.isFirstOrder()) {
            throw new IllegalArgumentException("Cannot make first-order equal to second-order or vice versa");
        }
        if (isFirstOrder()) {
            return Term.mkEq(getFirstOrderDecl().variable(), other.getFirstOrderDecl().variable());
        } else {
            FuncDecl func1 = getSecondOrderDecl();
            FuncDecl func2 = other.getSecondOrderDecl();
            //noinspection unchecked
            List<Sort> argSorts = CollectionConverters.<Sort> asJava(func1.argSorts());
            //noinspection unchecked
            if (!argSorts.equals(CollectionConverters.<Sort> asJava(func2.argSorts()))
                    || !func1.resultSort().equals(func2.resultSort())) {
                // TODO maybe short-circuit
                throw new IllegalArgumentException("Cannot makeEqual incompatible sorts");
            }

            List<Term> vars = new ArrayList<>();
            List<AnnotatedVar> annotatedVars = new ArrayList<>();
            for (Sort sort : argSorts) {
                Var var = Term.mkVar(nameGenerator.freshName("eqArg"));
                vars.add(var);
                annotatedVars.add(var.of(sort));
            }
            return Term.mkForall(annotatedVars, Term.mkEq(
                    Term.mkApp(func1.name(), vars), Term.mkApp(func2.name(), vars)));
        }
    }

}
