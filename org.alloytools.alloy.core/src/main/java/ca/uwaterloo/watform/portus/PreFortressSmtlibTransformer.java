package ca.uwaterloo.watform.portus;

import java.util.Optional;

/**
 * A hook into the SATFactory system to enable outputting pre-Fortress SMTLIB debug output.
 */
public class PreFortressSmtlibTransformer extends PortusSATFactory {

    public static final String ID = "fortress/raw-smtlib-pre";

    @Override
    public String id() {
        return ID;
    }

    @Override
    public String name() {
        return "Output SMTLIB+ (typechecking only) to file";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("SMTLIB+ is the Fortress debug output format. This outputs SMTLIB+ after only very few " +
                "Fortress transformers have modified the Fortress theory (typechecking only).");
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
