package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.interpretation.Interpretation;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.msfol.Var;
import fortress.operations.InterpretationVerifier;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import scala.collection.immutable.Seq;
import scala.jdk.javaapi.CollectionConverters;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public final class FortressSolution implements AlloySolution {

    /** The Fortress interpretation corresponding to this solution (null if unsat). */
    private final Interpretation interpretation;

    /** The translator used to produce the input to Fortress which produced the interpretation.. */
    private final Translator translator;

    /** The context of the translation used to produce the interpretation. */
    private final TranslationContext context;

    /** All reachable sigs in the model. */
    private final SafeList<Sig> sigs;

    private final String originalFilename;
    private final String originalCommand;

    /** Map atoms from Fortress to Alloy. */
    private final Map<Value, ExprVar> fortressToAlloyAtoms = new HashMap<>();

    /** The single Kodkod universe of atoms - Alloy requires a consistent Universe object. */
    private final Universe universe;

    FortressSolution(Interpretation interpretation, Translator translator, TranslationContext context,
                     Iterable<Sig> sigs, String originalFilename, String originalCommand) {
        this.interpretation = interpretation;
        this.translator = translator;
        this.context = context;
        this.sigs = new SafeList<>(sigs);
        this.originalFilename = originalFilename;
        this.originalCommand = originalCommand;

        if (interpretation != null) {
            // Generate Alloy atoms (ExprVars) for each Fortress atom
            // TODO - handle integers
            List<Value> fortressAtoms = interpretation.sortInterpretationsJava().get(context.univSort);
            for (Value atom : fortressAtoms) {
                ExprVar alloyAtom = ExprVar.make(null, atom.toString());
                fortressToAlloyAtoms.put(atom, alloyAtom);
            }
            this.universe = new Universe(fortressAtoms);
        } else {
            this.universe = null;
        }
    }

    @Override
    public int getBitwidth() {
        return context.getBitwidth();
    }

    @Override
    public int max() {
        return Util.max(getBitwidth());
    }

    @Override
    public int min() {
        return Util.min(getBitwidth());
    }

    @Override
    public int getMaxSeq() {
        return context.scoper.getMaxSeq();
    }

    @Override
    public int unrolls() {
        // TODO - recursion
        return 0;
    }

    @Override
    public int getMaxTrace() {
        // TODO - temporal support
        return -1;
    }

    @Override
    public int getMinTrace() {
        // TODO - temporal support
        return -1;
    }

    @Override
    public int getLoopState() {
        // TODO - temporal support
        return 0;
    }

    @Override
    public int getTraceLength() {
        // TODO - temporal support
        return 1;
    }

    @Override
    public String getOriginalFilename() {
        return originalFilename;
    }

    @Override
    public String getOriginalCommand() {
        return originalCommand;
    }

    @Override
    public boolean satisfiable() {
        return interpretation != null;
    }

    @Override
    public boolean hasConfigs() {
        // TODO - what is this?
        return false;
    }

    @Override
    public Iterable<ExprVar> getAllSkolems() {
        // TODO - skolemization
        return new ArrayList<>();
    }

    @Override
    public SafeList<Sig> getAllReachableSigs() {
        return sigs.dup();
    }

    @Override
    public Iterable<ExprVar> getAllAtoms() {
        return fortressToAlloyAtoms.values();
    }

    @Override
    public A4TupleSet eval(Sig sig) {
        return (A4TupleSet) eval((Expr) sig);
    }

    @Override
    public A4TupleSet eval(Sig sig, int state) {
        // TODO - temporal support
        return eval(sig);
    }

    @Override
    public A4TupleSet eval(Sig.Field field) {
        return (A4TupleSet) eval((Expr) field);
    }

    @Override
    public A4TupleSet eval(Sig.Field field, int state) {
        // TODO - temporal support
        return eval(field);
    }

    @Override
    public Object eval(Expr expr) throws Err {
        if (expr.type().is_bool) {
            // A formula - just check it and return the boolean
            // Translate to Fortress - copy the translation context to avoid any modifications
            TranslationContext contextCopy = new TranslationContext(context);
            Term fortressTerm = translator.translate(expr, contextCopy);
            return evaluateFormula(fortressTerm, interpretation);
        }

        // Check if it's an integer
        Expr intExpr = expr.typecheck_as_int();
        if (intExpr.errors.isEmpty()) {
            // Integer - TODO integers
            throw new ErrorAPI("Portus doesn't support integers yet, can't eval() int expression!");
        }

        // It's a tuple set - manually evaluate {(x1,...,xn) : univ^n | [[(x1,...,xn) \in expr]]}
        List<List<Value>> tupleSet = new ArrayList<>();
        Set<Value> atoms = fortressToAlloyAtoms.keySet();
        int arity = expr.type().arity();
        for (List<Value> tuple : cartesianPower(atoms, arity)) {
            // ExprElementOf only takes Vars, so use fake sorts to work around:
            // (x1,...,xn) \in expr --> forall y1: X1. ... forall yn: Xn. (y1,...,yn) \in expr
            // where X1 = {x1}, ..., Xn = {xn}
            // TODO - make ExprElementOf take Values
            List<Var> vars = tuple.stream()
                    .map(value -> Term.mkVar("var_" + value))
                    .collect(Collectors.toList());

            // Translate [[(y1,...,yn) \in expr]] - copy the context to avoid any modifications
            TranslationContext contextCopy = new TranslationContext(context);
            Expr inExpr = ExprElementOf.make(ConstList.make(vars), expr);
            Term formula = translator.translate(inExpr, contextCopy);

            // Add on the fake sorts (going backwards for elegance)
            Interpretation fakeSortInterp = interpretation;
            for (int i = 0; i < tuple.size(); i++) {
                Value value = tuple.get(i);
                Var var = vars.get(i);

                // Make and add the fake sort
                Sort fakeSort = Sort.mkSortConst("Sort_" + value);
                Seq<Value> fakeSortValue = CollectionConverters.asScala(
                        Collections.singletonList(value)).toList();
                fakeSortInterp = fakeSortInterp.updateSortInterpretations(fakeSort, fakeSortValue);

                // Add the forall onto the formula
                formula = Term.mkForall(var.of(fakeSort), formula);
            }

            boolean inSet = evaluateFormula(formula, fakeSortInterp);
            if (inSet) {
                tupleSet.add(tuple);
            }
        }

        // Convert the tuple set to the A4TupleSet that Alloy expects
        TupleFactory tupleFactory = universe.factory();
        List<Tuple> tuples = tupleSet.stream()
                .map(tupleFactory::tuple)
                .collect(Collectors.toList());
        TupleSet result;
        if (tuples.isEmpty()) {
            // TupleFactory.setOf() can't determine the arity if there are no tuples
            result = tupleFactory.noneOf(arity);
        } else {
            result = tupleFactory.setOf(tuples);
        }
        return new A4TupleSet(result, this);
    }

    @Override
    public Object eval(Expr expr, int state) throws Err {
        // TODO - temporal support
        return eval(expr);
    }

    // Is 'formula' true in the interpretation?
    private static boolean evaluateFormula(
            Term formula, Interpretation interpretation) {
        // Check whether the interpretation satisfies a theory with the term as the only axiom.
        Theory theory = Theory.empty()
                .withSorts(interpretation.sortInterpretationsJava().keySet())
                .withFunctionDeclarations(interpretation.functionInterpretations().keys())
                .withConstants(interpretation.constantInterpretationsJava().keySet())
                .withAxiom(formula);
        InterpretationVerifier verifier = new InterpretationVerifier(theory);
        return verifier.verifyInterpretation(interpretation);
    }

    // Compute values^n recursively (i.e., all n-tuples of elements of values), n >= 0.
    private Set<List<Value>> cartesianPower(Set<Value> values, int n) {
        if (n == 0) {
            // Singleton list with just ()
            return Collections.singleton(new ArrayList<>());
        } else {
            // Compute (values^{n-1}) x values
            Set<List<Value>> prev = cartesianPower(values, n-1);
            Set<List<Value>> result = new HashSet<>();
            for (List<Value> tuple : prev) {
                for (Value value : values) {
                    List<Value> addedTuple = new ArrayList<>(tuple);
                    addedTuple.add(value);
                    result.add(addedTuple);
                }
            }
            return result;
        }
    }

    @Override
    public String toString() {
        // TODO - do we need to do this?
        return satisfiable() ? "SAT" : "UNSAT";
    }

    @Override
    public String toString(int state) {
        // TODO - temporal support
        return toString();
    }

    @Override
    public A4Solution next() throws Err {
        // TODO - does Fortress support incremental solving?
        throw new ErrorAPI("Not an incremental solver!");
    }

    @Override
    public A4Solution fork(int p) throws Err {
        // TODO - does Fortress support incremental solving?
        throw new ErrorAPI("Not an incremental solver!");
    }

    @Override
    public boolean isIncremental() {
        // TODO - does Fortress support incremental solving?
        return false;
    }

    @Override
    public Set<Pos> lowLevelCore() {
        // TODO - does Fortress support unsat cores?
        return Collections.emptySet();
    }

    @Override
    public Pair<Set<Pos>, Set<Pos>> highLevelCore() {
        // TODO - does Fortress support unsat cores?
        return new Pair<>(Collections.emptySet(), Collections.emptySet());
    }

    @Override
    public void writeXML(String filename) throws Err {
        writeXML(A4Reporter.NOP, filename, Collections.emptyList(), Collections.emptyMap());
    }

    @Override
    public void writeXML(
            A4Reporter rep, String filename, Iterable<Func> macros, Map<String, String> sourceFiles) throws Err {
        System.out.println(filename);
        try (PrintWriter out = new PrintWriter(filename, "UTF-8")) {
            writeXML(rep, out, macros, sourceFiles);
            if (out.checkError()) {
                throw new ErrorFatal("Failed to write the Fortress solution XML file.");
            }
        } catch (IOException e) {
            throw new ErrorFatal("Error writing the Fortress solution XML file.", e);
        }
    }

    @Override
    public void writeXML(PrintWriter writer, Iterable<Func> macros, Map<String, String> sourceFiles) throws Err {
        writeXML(A4Reporter.NOP, writer, macros, sourceFiles);
    }

    private void writeXML(
            A4Reporter rep, PrintWriter writer, Iterable<Func> macros, Map<String, String> sourceFiles) throws Err {
        // Use the general solution writer routine
        A4SolutionWriter.writeInstance(rep, this, writer, macros, sourceFiles);
    }

    @Override
    public String format() {
        // TODO - do we need to do this?
        return null;
    }

    @Override
    public String format(int state) {
        // TODO - temporal support
        return format();
    }

    @Override
    public String atom2name(Object atom) {
        return atom.toString();
    }

    @Override
    public Sig.PrimSig atom2sig(Object atom) {
        // TODO: find the sig of an atom (brute force?)
        return null;
    }

}
