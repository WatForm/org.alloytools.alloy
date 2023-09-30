package ca.uwaterloo.watform.portus;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

/**
 * Performs all the data collection needed for the paper.
 */
public class PortusStatistics {

    private final Map<Translator, Integer> translatorUsageCounts = new HashMap<>();

    public void incrementUsageCount(Translator translator) {
        if (!translatorUsageCounts.containsKey(translator)) {
            translatorUsageCounts.put(translator, 0);
        }
        translatorUsageCounts.put(translator, translatorUsageCounts.get(translator) + 1);
    }

    private final Map<ScalarCaster, Integer> scalarCasterUsageCounts = new HashMap<>();

    public void incrementUsageCount(ScalarCaster scalarCaster) {
        if (!scalarCasterUsageCounts.containsKey(scalarCaster)) {
            scalarCasterUsageCounts.put(scalarCaster, 0);
        }
        scalarCasterUsageCounts.put(scalarCaster, scalarCasterUsageCounts.get(scalarCaster) + 1);
    }

    private int elementOfScalarCasterIgnoredDueToFreeVarsCount = 0;

    public void incrementElementOfScalarCasterIgnoredDueToFreeVarsCount() {
        elementOfScalarCasterIgnoredDueToFreeVarsCount++;
    }

    public int getElementOfScalarCasterIgnoredDueToFreeVarsCount() {
        return elementOfScalarCasterIgnoredDueToFreeVarsCount;
    }

    private int translationCacheHitCount = 0;

    public void incrementTranslationCacheHitCount() {
        translationCacheHitCount++;
    }

    public int getTranslationCacheHitCount() {
        return translationCacheHitCount;
    }

    private int castToScalarCacheHitCount = 0;

    public void incrementCastToScalarCacheHitCount() {
        castToScalarCacheHitCount++;
    }

    public int getCastToScalarCacheHitCount() {
        return castToScalarCacheHitCount;
    }

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
        translatorUsageCounts.entrySet().stream()
                .sorted(Comparator.comparing(entry -> entry.getKey().name(), String::compareToIgnoreCase))
                .forEach(entry -> {
                    System.out.print(indent + indent);
                    System.out.print(entry.getKey().name());
                    System.out.print(": ");
                    System.out.println(entry.getValue());
                });
        System.out.println(indent + "Scalar caster usage counts:");
        scalarCasterUsageCounts.entrySet().stream()
                .sorted(Comparator.comparing(entry -> entry.getKey().name(), String::compareToIgnoreCase))
                .forEach(entry -> {
                    System.out.print(indent + indent);
                    System.out.print(entry.getKey().name());
                    System.out.print(": ");
                    System.out.println(entry.getValue());
                });
        System.out.println(indent + "Times element-of scalar caster couldn't optimize due to free vars: "
                + getElementOfScalarCasterIgnoredDueToFreeVarsCount());
        if (options.enableCaching) {
            System.out.println(indent + "Translation cache hits: " + getTranslationCacheHitCount());
            System.out.println(indent + "Cast-to-scalar cache hits: " + getCastToScalarCacheHitCount());
        }
        System.out.println(indent + "Portus time: " + portusStopwatch.formatDuration());
        System.out.println(indent + "SMT solver time: " + smtSolverStopwatch.formatDuration());
    }

}
