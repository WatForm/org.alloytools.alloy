package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.Err;

/**
 * An error indicating that the model uses a feature that Portus does not support.
 * This is separate from ErrorFatal so that errors of this type can be treated differently
 * than errors indicating a correctness issue.
 */
public class ErrorNoPortusSupport extends Err {

    /** This ensures this class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    public ErrorNoPortusSupport(String cause) {
        super(null, cause, null);
    }

    @Override
    public String toString() {
        return "Portus does not support an Alloy feature that was used:\n" + msg;
    }

}
