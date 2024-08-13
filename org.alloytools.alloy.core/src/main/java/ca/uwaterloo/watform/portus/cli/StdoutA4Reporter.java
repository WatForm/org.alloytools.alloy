package ca.uwaterloo.watform.portus.cli;

import edu.mit.csail.sdg.alloy4.A4Reporter;

/**
 * An {@link A4Reporter} implementation that prints to standard output for debugging purposes.
 */
class StdoutA4Reporter extends A4Reporter {

    private final boolean verbose;

    public StdoutA4Reporter(boolean verbose) {
        this.verbose = verbose;
    }

    @Override
    public void debug(String msg) {
        if (verbose) {
            System.out.println("[fortress] " + msg);
        }
    }

}
