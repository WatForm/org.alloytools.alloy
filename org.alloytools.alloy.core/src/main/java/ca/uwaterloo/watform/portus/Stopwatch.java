package ca.uwaterloo.watform.portus;

import java.lang.management.ManagementFactory;

/**
 * A single-shot stopwatch that measures CPU time.
 */
final class Stopwatch {

    private enum State {
        NOT_STARTED,
        RUNNING,
        STOPPED,
    }

    private State state = State.NOT_STARTED;

    private long startTimestampNs = -1;
    private long durationNs = -1;

    private long getTimestampNs() {
        // Use CPU time and not wall-clock time
        long threadId = Thread.currentThread().getId();
        return ManagementFactory.getThreadMXBean().getThreadCpuTime(threadId);
    }

    public void start() {
        if (state != State.NOT_STARTED) {
            throw new IllegalStateException("Stopwatch previously started, cannot start!");
        }
        startTimestampNs = getTimestampNs();
        state = State.RUNNING;
    }

    public void stop() {
        if (state != State.RUNNING) {
            throw new IllegalStateException("Stopwatch not running, cannot stop!");
        }
        durationNs = getTimestampNs() - startTimestampNs;
        state = State.STOPPED;
    }

    public long getDurationInNanoseconds() {
        if (state != State.STOPPED) {
            throw new IllegalStateException("Stopwatch has not run, cannot get duration!");
        }
        return durationNs;
    }

    private String formatNanoseconds(long ns) {
        StringBuilder builder = new StringBuilder();
        long nsPerHour = 1000000000L * 60L * 60L;
        long hours = ns / nsPerHour;
        if (hours > 0) {
            builder.append(hours);
            builder.append("h");
        }
        ns %= nsPerHour;

        long nsPerMinute = 1000000000L * 60L;
        long mins = ns / nsPerMinute;
        if (mins > 0) {
            builder.append(mins);
            builder.append("m");
        }
        ns %= nsPerMinute;

        long nsPerSecond = 1000000000L;
        double secs = (double) ns / nsPerSecond;
        builder.append(String.format("%.3f", secs));
        builder.append("s");
        return builder.toString();
    }

    public String formatDuration() {
        switch (state) {
            case NOT_STARTED:
            default:
                return "(not started)";
            case RUNNING:
                return "(running)";
            case STOPPED:
                return formatNanoseconds(durationNs);
        }
    }

}
