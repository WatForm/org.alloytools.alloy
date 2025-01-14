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
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.AlloySolution;
import fortress.interpretation.Interpretation;
import fortress.msfol.AnnotatedVar;
import fortress.msfol.FuncDecl;
import fortress.msfol.FunctionDefinition;
import fortress.msfol.IntegerLiteral;
import fortress.msfol.Sort;
import fortress.msfol.Term;
import fortress.msfol.Theory;
import fortress.msfol.Value;
import fortress.operations.PreimageFinding;
import fortress.operations.InterpretationVerifier;
import kodkod.instance.Universe;
import scala.Option;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class FortressSolution implements AlloySolution {

    /** The Fortress interpretation corresponding to this solution (null if unsat). */
    private final Interpretation interpretation;

    /** An evaluator which contains the state necessary to evaluate expressions in this interpretation. */
    private final Evaluator evaluator;

    /** The context of the translation used to produce the interpretation. */
    private final TranslationContext context;

    /** All reachable sigs in the model. */
    private final SafeList<Sig> sigs;

    private final String originalFilename;
    private final String originalCommand;
    private final A4Options originalOptions;

    /** Map atoms from Fortress to Alloy. */
    private final Map<Value, ExprVar> fortressToAlloyAtoms = new HashMap<>();

    /** Map sorts to the atoms that belong to them. */
    private final Map<Sort, List<Value>> sortsToAtoms = new HashMap<>();

    /** The single Kodkod universe of atoms - Alloy requires a consistent Universe object. */
    private final Universe universe;

    FortressSolution(Interpretation interpretation, Evaluator evaluator, TranslationContext context, Iterable<Sig> sigs,
                     String originalFilename, String originalCommand, A4Options originalOptions) {
        this.interpretation = interpretation;
        this.evaluator = evaluator;
        this.context = context;
        this.sigs = new SafeList<>(sigs);
        this.originalFilename = originalFilename;
        this.originalCommand = originalCommand;
        this.originalOptions = originalOptions;

        if (interpretation != null) {
            // Generate Alloy atoms (ExprVars) for each Fortress atom
            Map<Sort, List<Value>> sortInterpretations = new HashMap<>(interpretation.sortInterpretationsJava());

            // Manually include integers if they aren't already included
            if (!sortInterpretations.containsKey(Sort.Int())) {
                int bitwidth = context.getBitwidth();
                sortInterpretations.put(Sort.Int(), IntStream.range(Util.min(bitwidth), Util.max(bitwidth) + 1)
                        .mapToObj(IntegerLiteral::apply)
                        .collect(Collectors.toList()));
            }

            List<Value> fortressAtoms = new ArrayList<>();
            for (Sort sort : sortInterpretations.keySet()) {
                // Booleans will cause an error if they're included in the universe, so manually exclude them if needed
                if (Objects.equals(sort, Sort.Bool())) {
                    continue;
                }

                List<Value> sortAtoms = sortInterpretations.get(sort);
                fortressAtoms.addAll(sortAtoms);
                sortsToAtoms.put(sort, sortAtoms);
                for (Value atom : sortAtoms) {
                    ExprVar alloyAtom = ExprVar.make(null, atom.toString());
                    fortressToAlloyAtoms.put(atom, alloyAtom);
                }
            }
            List<Object> sanitizedLiterals = sanitizeLiteralsForKodkod(fortressAtoms);

            // Kodkod can't handle an empty universe, so A4Solution adds a "<empty>" literal: mimic this
            if (sanitizedLiterals.isEmpty()) {
                sanitizedLiterals.add("<empty>");
            }

            this.universe = new Universe(sanitizedLiterals);
        } else {
            this.universe = null;
        }
    }

    List<Value> getSortAtoms(Sort sort) {
        return sortsToAtoms.get(sort);
    }

    Universe getUniverse() {
        return universe;
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
    public A4Options getOptions() {
        return originalOptions;
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
    public List<ExprVar> getAllSkolems() {
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
        ValueTupleSet tupleSet = evaluator.evaluate(expr, this, context);

        // Pure booleans and ints are expected to be returned as Java booleans and ints.
        if (tupleSet.isPureBoolean()) {
            return tupleSet.getPureBoolean();
        }
        if (tupleSet.isPureInt()) {
            return tupleSet.getPureInt();
        }

        return tupleSet.toAlloy(this);
    }

    @Override
    public Object eval(Expr expr, int state) throws Err {
        // TODO - temporal support
        return eval(expr);
    }

    /** Is this given Fortress formula true in this theory's interpretation? It must be a boolean formula. */
    boolean evaluateFormula(Term formula) {
        // Check whether the interpretation satisfies a theory with the term as the only axiom.
        Theory theory = Theory.empty()
                .withSorts(interpretation.sortInterpretationsJava().keySet())
                .withFunctionDeclarations(interpretation.functionInterpretations().keys())
                .withConstantDeclarations(interpretation.constantInterpretationsJava().keySet())
                .withAxiom(formula);
        InterpretationVerifier verifier = new InterpretationVerifier(theory);
        return verifier.verifyInterpretation(interpretation);
    }

    /**
     * Find the Value this term is interpreted as.
     * Note: This does not support quantifiers. Use evaluateFormula for general formulas.
     */
    Value evaluateTerm(Term term) {
        return interpretation.visitFunctionBody(term, scala.collection.immutable.Map$.MODULE$.<Term, Value>empty());
    }

    /**
     * Get the preimage of the output value in the function func.
     */
    ValueTupleSet functionPreimage(FuncDecl func, Value output) {
        // Note: a Map is the wrong data structure for this! This is very inefficient, no better than naive iteration!
        // Functions should always show up in the function interpretations, even if it's filled by a definition
        if (!interpretation.functionInterpretationsJava().containsKey(func)) {
            throw new ErrorFatal("Function " + func + " does not exist in this solution!");
        }

        ValueTupleSet result = interpretation.functionInterpretationsJava().get(func).entrySet().stream()
                .filter(entry -> Objects.equals(entry.getValue(), output))
                .map(Map.Entry::getKey)
                .collect(ValueTupleSet.collect(func.arity()));

        // If there's a function definition, include it too
        Option<FunctionDefinition> definitionOption = interpretation.functionDefinitions().find(
                def -> def.name().equals(func.name())
                        && def.argSortedVar().map(AnnotatedVar::sort).equals(func.argSorts())
                        && def.resultSort().equals(func.resultSort()));
        if (definitionOption.isDefined()) {
            FunctionDefinition definition = definitionOption.get();
            int arity = definition.argSortedVar().size();
            result = result.union(ValueTupleSet.fromScala(PreimageFinding.findPreimage(interpretation,
                    definition.argSortedVar(),
                    definition.body(),
                    output), arity));
        }

        return result;
    }

    // A4SolutionReader/Writer want the int literals to be actual Integer objects, so convert IntegerLiterals.
    // TODO: duplicates ValueTupleSet
    private List<Object> sanitizeLiteralsForKodkod(List<Value> values) {
        return values.stream()
                .map(value -> {
                    if (value instanceof IntegerLiteral) {
                        return ((IntegerLiteral) value).value();
                    } else if (Term.mkTop().equals(value) || Term.mkBottom().equals(value)) {
                        throw new ErrorFatal("Booleans are invalid in Kodkod tuples!");
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
