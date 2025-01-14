package ca.uwaterloo.watform.portus;

import java.util.Optional;

/**
 * A hook into the SATFactory system to enable outputting pre-Fortress SMTLIB debug output.
 */
public class PostFortressSmtlibTransformer extends PortusSATFactory {

    public static final String ID = "fortress/raw-smtlib-post";

    @Override
    public String id() {
        return ID;
    }

    @Override
    public String name() {
        return "Output SMTLIB+ (post-Fortress) to file";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("SMTLIB+ is the Fortress debug output format. This outputs SMTLIB+ after all the Fortress " +
                "transformers in use have run.");
    }

    @Override
    public String type() {
        return "transformer";
    }

    @Override
    public boolean isTransformer() {
        return true;
    }

}
