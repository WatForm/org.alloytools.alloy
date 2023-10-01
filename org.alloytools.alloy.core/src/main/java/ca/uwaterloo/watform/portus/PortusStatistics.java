package ca.uwaterloo.watform.portus;

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
    private final Stopwatch smtSolverStopwatch = new Stopwatch();

    public void onStartPortus() {
        portusStopwatch.start();
    }

    public void onPortusFinished() {
        portusStopwatch.stop();
    }

    public void onStartSmtSolver() {
        smtSolverStopwatch.start();
    }

    public void onSmtSolverFinished() {
        smtSolverStopwatch.stop();
    }

    public void printSummary(PortusOptions options) {
        final String indent = "  ";
        System.out.println("Statistics summary:");
        System.out.println(indent + "Translator usage counts:");
        translatorUsageCounts.print(indent + indent, Translator::name);
        System.out.println(indent + "Scalar caster usage counts:");
        scalarCasterUsageCounts.print(indent + indent, ScalarCaster::name);
        System.out.println(indent + "Times element-of scalar caster couldn't optimize due to free vars: "
                + elementOfScalarCasterIgnoredDueToFreeVarsCount.count);
        if (options.enableCaching) {
            System.out.println(indent + "Translation cache hits: " + translationCacheHitCount.count);
            System.out.println(indent + "Cast-to-scalar cache hits: " + castToScalarCacheHitCount.count);
        }
        System.out.println(indent + "Portus time: " + portusStopwatch.formatDuration());
        System.out.println(indent + "SMT solver time: " + smtSolverStopwatch.formatDuration());
    }

}
