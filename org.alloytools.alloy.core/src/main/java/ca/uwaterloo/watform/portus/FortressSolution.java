package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;
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
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.interpretation.Interpretation;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.operations.InterpretationVerifier;
import fortress.operations.Substituter;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

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
import java.util.stream.IntStream;

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

    /** Get the sort of any Fortress atom. */
    private final Map<Value, Sort> atomsToSorts = new HashMap<>();

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
            Map<Sort, List<Value>> sortInterpretations = new HashMap<>(interpretation.sortInterpretationsJava());

            // Manually include integers if they aren't already included
            if (!sortInterpretations.containsKey(Sort.Int())) {
                // TODO: is it okay to specify *which* integers are included like this?
                int intScope = context.getIntScope();
                sortInterpretations.put(Sort.Int(), IntStream.range(-intScope/2, intScope/2)
                        .mapToObj(IntegerLiteral::apply)
                        .collect(Collectors.toList()));
            }

            List<Value> fortressAtoms = new ArrayList<>();
            for (Sort sort : sortInterpretations.keySet()) {
                List<Value> sortAtoms = sortInterpretations.get(sort);
                fortressAtoms.addAll(sortAtoms);
                for (Value atom : sortAtoms) {
                    ExprVar alloyAtom = ExprVar.make(null, atom.toString());
                    fortressToAlloyAtoms.put(atom, alloyAtom);
                    atomsToSorts.put(atom, sort);
                }
            }
            this.universe = new Universe(sanitizeIntLiteralsForKodkod(fortressAtoms));
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
            throw new ErrorAPI("Can't eval() int expression!");
        }

        // It's a tuple set - manually evaluate {(x1,...,xn) : sorts | [[(x1,...,xn) \in expr]]}
        List<List<Value>> tupleSet = new ArrayList<>();
        Set<Value> atoms = fortressToAlloyAtoms.keySet();
        int arity = expr.type().arity();
        for (List<Value> tuple : cartesianPower(atoms, arity)) {
            // ExprElementOf only takes Vars, so use tricks to get around:
            // for (v1,...,vn) \in expr, make vars x1,...,xn and translate [[(x1,...,xn) \in expr]]
            // and then substitute xi->vi for i=1..n.
            List<AnnotatedVar> vars = tuple.stream()
                    .map(atom -> Term.mkVar("var_" + atom).of(atomsToSorts.get(atom)))
                    .collect(Collectors.toList());

            TranslationContext contextCopy = new TranslationContext(context);
            Expr inExpr = ExprElementOf.make(new VarTuple(vars), expr);
            Term formula = translator.translate(inExpr, contextCopy);

            // Substitute for the values we want to evaluate
            for (int i = 0; i < tuple.size(); i++) {
                formula = Substituter.apply(
                        vars.get(i).variable(), tuple.get(i), formula, contextCopy.nameGenerator);
            }

            boolean inSet = evaluateFormula(formula, interpretation);
            System.out.println(inExpr + " | " + formula + " | " + inSet);
            if (inSet) {
                tupleSet.add(tuple);
            }
        }

        // A4SolutionWriter/Reader don't process Int normally but instead assume that int literals are represented
        // by actual integers - so make sure that's the case.
        List<List<Object>> processedTuples = tupleSet.stream()
                .map(this::sanitizeIntLiteralsForKodkod)
                .collect(Collectors.toList());

        // Convert the tuple set to the A4TupleSet that Alloy expects
        TupleFactory tupleFactory = universe.factory();
        List<Tuple> tuples = processedTuples.stream()
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

    // A4SolutionReader/Writer want the int literals to be actual Integer objects, so convert IntegerLiterals.
    private List<Object> sanitizeIntLiteralsForKodkod(List<Value> values) {
        return values.stream()
                .map(value -> {
                    if (value instanceof IntegerLiteral) {
                        return ((IntegerLiteral) value).value();
                    } else {
                        return value;
                    }
                })
                .collect(Collectors.toList());
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
        return interpretation.toString();
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
        // For now, brute force which sig it's in by manually loading each sig's atoms
        // TODO: if this is hurting perf, cache the sigs' atoms
        for (Sig sig : getAllReachableSigs()) {
            if (sig instanceof Sig.PrimSig) {
                A4TupleSet sigAtoms = eval(sig);
                for (A4Tuple tuple : sigAtoms) {
                    assert tuple.arity() == 1;
                    if (tuple.atom(0).equals(atom.toString())) {
                        return (Sig.PrimSig) sig;
                    }
                }
            }
        }
        return Sig.UNIV; // didn't find it
    }

}
