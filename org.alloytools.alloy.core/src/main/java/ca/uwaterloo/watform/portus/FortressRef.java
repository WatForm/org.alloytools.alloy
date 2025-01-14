package ca.uwaterloo.watform.portus;

import java.util.Optional;

public class FortressRef extends PortusSATFactory {

    public static final String ID = "fortress/z3";

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return ID;
    }

    @Override
    public String name() {
        return "Fortress/Z3";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Fortress is a library for performing finite model finding over equality with " +
                "uninterpreted functions (EUF). This solver uses Z3 as the underlying SMT solver.");
    }

    @Override
    public String type() {
        return "java";
    }

}
