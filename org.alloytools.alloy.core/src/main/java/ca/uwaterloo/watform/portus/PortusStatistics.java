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

    public void printSummary() {
        final String indent = "  ";
        System.out.println("Summary:");
        System.out.println(indent + "Translator usage counts:");
        translatorUsageCounts.entrySet().stream()
                .sorted(Comparator.comparing(entry -> entry.getKey().name(), String::compareToIgnoreCase))
                .forEach(entry -> {
                    System.out.print(indent + indent);
                    System.out.print(entry.getKey().name());
                    System.out.print(": ");
                    System.out.println(entry.getValue());
                });
    }

}
