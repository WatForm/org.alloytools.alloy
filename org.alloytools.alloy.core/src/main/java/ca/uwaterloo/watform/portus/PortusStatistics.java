package ca.uwaterloo.watform.portus;

import fortress.msfol.Theory;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * Performs all the data collection needed for the paper.
 * Objects should have no side effects outside of the explicit output functions like printSummary().
 */
public final class PortusStatistics {

    public static final class UsageCounts<T> {
        private final Map<T, Integer> usageCounts = new HashMap<>();

        public void increment(T t) {
            if (!usageCounts.containsKey(t)) {
                usageCounts.put(t, 0);
            }
            usageCounts.put(t, usageCounts.get(t) + 1);
        }

        @SuppressWarnings("SameParameterValue")
        private void print(String indent, Function<T, String> namer) {
            if (usageCounts.isEmpty()) {
                System.out.println(indent + "(none)");
                return;
            }
            usageCounts.entrySet().stream()
                    .sorted(Comparator.comparing(entry -> namer.apply(entry.getKey()), String::compareToIgnoreCase))
                    .forEach(entry -> {
                        System.out.print(indent);
                        System.out.print(namer.apply(entry.getKey()));
                        System.out.print(": ");
                        System.out.println(entry.getValue());
                    });
        }
    }

    public static final class Counter {
        private int count = 0;

        public void increment() {
            count++;
        }
    }

    public final UsageCounts<Translator> translatorUsageCounts = new UsageCounts<>();
    public final UsageCounts<ScalarCaster> scalarCasterUsageCounts = new UsageCounts<>();

    public final Counter elementOfScalarCasterIgnoredDueToFreeVarsCount = new Counter();
    public final Counter translationCacheHitCount = new Counter();
    public final Counter castToScalarCacheHitCount = new Counter();

    private final Stopwatch portusStopwatch = new Stopwatch();
    private final Stopwatch translationStopwatch = new Stopwatch();
    private final Stopwatch smtSolverStopwatch = new Stopwatch();
    private final Stopwatch kodkodStopwatch = new Stopwatch();

    public void onStartPortus() {
        portusStopwatch.start();
    }

    public void onPortusFinished() {
        portusStopwatch.stop();
    }

    public void onStartTranslation() {
        translationStopwatch.start();
    }

    public void onTranslationFinished() {
        translationStopwatch.stop();
    }

    public void onStartSmtSolver() {
        smtSolverStopwatch.start();
    }

    public void onSmtSolverFinished() {
        smtSolverStopwatch.stop();
    }

    public void onStartKodkod() {
        kodkodStopwatch.start();
    }

    public void onKodkodFinished() {
        kodkodStopwatch.stop();
    }

    private boolean hasTheoryStats = false;
    private int theorySortCount = -1;
    private int theoryFuncCount = -1;
    private int theoryConstCount = -1;
    private int theoryAxiomCount = -1;
    private int theorySymbolCount = -1;

    /** Quickly print a theory's stats for debugging purposes. */
    public static void printTheoryStats(Theory theory) {
        PortusStatistics statistics = new PortusStatistics();
        statistics.setTheoryStats(theory);
        statistics.printTheoryStats("");
    }

    public void setTheoryStats(Theory theory) {
        hasTheoryStats = true;
        theorySortCount = theory.sorts().size();
        theoryFuncCount = theory.functionDeclarations().size();
        theoryConstCount = theory.constantDeclarations().size();
        theoryAxiomCount = theory.axioms().size();
        theorySymbolCount = PortusUtil.countSymbols(theory);
    }

    private void printTheoryStats(String indent) {
        if (!hasTheoryStats) {
            System.out.println(indent + "(none)");
            return;
        }

        System.out.println(indent + "Sorts: " + theorySortCount);
        System.out.println(indent + "Functions: " + theoryFuncCount);
        System.out.println(indent + "Constants: " + theoryConstCount);
        System.out.println(indent + "Axioms: " + theoryAxiomCount);
        System.out.println(indent + "Symbols: " + theorySymbolCount);
    }

    public void printSummary(PortusOptions options) {
        final String indent = "  ";
        System.out.println("Statistics summary:");

        System.out.println(indent + "Theory statistics:");
        printTheoryStats(indent + indent);

        System.out.println(indent + "Translator usage counts:");
        translatorUsageCounts.print(indent + indent, Translator::name);

        System.out.println(indent + "Scalar caster usage counts:");
        scalarCasterUsageCounts.print(indent + indent, ScalarCaster::name);

        if (options.enableElementOfScalarOptimization) {
            System.out.println(indent + "Times element-of scalar caster couldn't optimize due to free vars: "
                    + elementOfScalarCasterIgnoredDueToFreeVarsCount.count);
        }

        if (options.enableCaching) {
            System.out.println(indent + "Translation cache hits: " + translationCacheHitCount.count);
            System.out.println(indent + "Cast-to-scalar cache hits: " + castToScalarCacheHitCount.count);
        }

        if (portusStopwatch.hasRun()) {
            System.out.println(indent + "Portus time: " + portusStopwatch.formatDuration());
        }
        if (translationStopwatch.hasRun()) {
            System.out.println(indent + "Portus translation time: " + translationStopwatch.formatDuration());
        }
        if (smtSolverStopwatch.hasRun()) {
            System.out.println(indent + "SMT solver time: " + smtSolverStopwatch.formatDuration());
        }
        if (kodkodStopwatch.hasRun()) {
            System.out.println(indent + "Kodkod time: " + kodkodStopwatch.formatDuration());
        }
    }

}
