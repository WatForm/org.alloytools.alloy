package ca.uwaterloo.watform.portus;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

import java.util.List;

/**
 * A marker subclass of SATFactory for solvers which should be handled by Portus instead.
 */
public abstract class PortusSATFactory extends SATFactory {

    /**
     * Add Portus's solvers and transformers. Called by the dispatcher on startup.
     */
    public static void addPortusExtensions(List<SATFactory> extensions) {
        extensions.add(new FortressRef());
        extensions.add(new FortressMSFOLTransformer());
        extensions.add(new PreFortressSmtlibTransformer());
        extensions.add(new PostFortressSmtlibTransformer());
    }

    public TranslateAlloyToFortress getCommandRunner() {
        return new TranslateAlloyToFortress();
    }

    @Override
    protected SATSolver createSolver() {
        throw new UnsupportedOperationException(this + " is an SMT solver and should be handled by Portus. It cannot " +
                "create instances");
    }

    @Override
    public boolean isPresent() {
        // avoid trying to create an instance
        return true;
    }

}
