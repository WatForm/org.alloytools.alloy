package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Options;
import fortress.interpretation.BasicInterpretation$;
import fortress.interpretation.Interpretation;
import fortress.modelfinders.ErrorResult;
import fortress.modelfinders.ModelFinder;
import fortress.modelfinders.ModelFinderResult;
import fortress.msfol.*;
import scala.collection.immutable.Seq;
import scala.jdk.javaapi.CollectionConverters;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * A wrapper over a ModelFinder which returns a FortressSolution, encapsulating the process of postprocessing
 * a ModelFinderResult into a FortressSolution.
 * Keeps the solver process open until close() is called - must be closed when done!
 */
class SolutionFinder implements AutoCloseable {

    private final ModelFinder modelFinder;

    private final TranslationResult translated;

    private final Module world;
    private final Command command;
    private final A4Options options;

    private final PortusStatistics statistics;

    public SolutionFinder(ModelFinder modelFinder, TranslationResult translated, Module world, Command command,
                          A4Options options, PortusStatistics statistics) {
        this.modelFinder = modelFinder;
        this.translated = translated;
        this.world = world;
        this.command = command;
        this.options = options;
        this.statistics = statistics;
    }

    public FortressSolution solve() {
        statistics.onStartSmtSolver();
        ModelFinderResult result;
        try {
            result = modelFinder.checkSat(false, false);
        } finally {
            statistics.onSmtSolverFinished();
        }
        return processResult(result);
    }

    public FortressSolution nextInterpretation() {
        // TODO - not running statistics SMT solver stopwatch because can't restart those! Reset it?
        return processResult(modelFinder.nextInterpretation());
    }

    private FortressSolution processResult(ModelFinderResult result) {
        if (result instanceof ErrorResult) {
            throw new ErrorFatal("Fortress error: " + ((ErrorResult) result).message());
        }
        if (result == ModelFinderResult.Timeout()) {
            throw new TimeoutException();
        }
        if (result == ModelFinderResult.Unknown()) {
            throw new ErrorFatal("Fortress returned UNKNOWN!");
        }

        Interpretation interpretation = (result == ModelFinderResult.Sat())
                ? postprocessInterp(modelFinder.viewModel(), translated) : null;
        return new FortressSolution(interpretation, translated.getEvaluator(), translated.getStringDecoder(),
                translated.getContext(), world.getAllReachableSigs(), options.originalFilename, command.toString(),
                this);
    }

    private Interpretation postprocessInterp(Interpretation interpretation, TranslationResult translated) {
        // Add Int if it's not already there (sometimes it isn't)
        Map<Sort, List<Value>> sortInterpretations = new HashMap<>(interpretation.sortInterpretationsJava());
        if (!sortInterpretations.containsKey(Sort.Int())) {
            int bitwidth = translated.getBitwidth();
            sortInterpretations.put(Sort.Int(), IntStream.range(Util.min(bitwidth), Util.max(bitwidth) + 1)
                    .mapToObj(IntegerLiteral::apply)
                    .collect(Collectors.toList()));
        }
        // Convert back to Scala types
        Map<Sort, Seq<Value>> sortInterpretationsScala = new HashMap<>();
        for (Sort sort : sortInterpretations.keySet()) {
            sortInterpretationsScala.put(sort, PortusUtil.toScalaSeq(sortInterpretations.get(sort)));
        }

        // If any function declarations are missing, add them back as arbitrary
        // Z3 sometimes doesn't return functions when they're completely optimized out
        Set<FunctionDefinition> newFuncDefs = new HashSet<>();
        translated.getTheory().functionDeclarations().foreach(funcDecl -> {
            if (interpretation.functionDefinitions().find(def -> def.name().equals(funcDecl.name())).isEmpty()) {
                List<AnnotatedVar> args = new ArrayList<>();
                for (int i = 0; i < funcDecl.argSorts().size(); i++) {
                    args.add(AnnotatedVar.apply(Term.mkVar("x" + i), funcDecl.argSorts().apply(i)));
                }
                Term body;
                if (funcDecl.resultSort().equals(Sort.Bool())) {
                    body = Term.mkBottom();
                } else {
                    body = Term.mkDomainElement(1, funcDecl.resultSort());
                }
                FunctionDefinition funcDef = FunctionDefinition.mkFunctionDefinition(
                        funcDecl.name(), args, funcDecl.resultSort(), body);
                newFuncDefs.add(funcDef);
            }
            return null;
        });
        scala.collection.immutable.Set<FunctionDefinition> newFuncDefsSet = CollectionConverters.asScala(newFuncDefs)
                .<FunctionDefinition>toSet();

        // Add the function definitions from the theory because they aren't returned from Fortress
        //noinspection unchecked
        return BasicInterpretation$.MODULE$.apply(
                PortusUtil.toScalaMap(sortInterpretationsScala),
                interpretation.constantInterpretations(),
                interpretation.functionDefinitions().concat(translated.getTheory().functionDefinitions())
                        .concat(newFuncDefsSet).toSet());
    }

    @Override
    public void close() {
        modelFinder.close();
    }

}
