package kodkod.solvers;

import java.util.Optional;

import org.sat4j.minisat.SolverFactory;

import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

public class SAT4JRef extends SATFactory {
	private static final long serialVersionUID = 1L;
	private static SATFactory instance = null;

	// [portus] Initialize lazily to avoid issues related to static load order when initializing SATFactory.DEFAULT
	// which occur when running the Portus CLI
	public static SATFactory getRefInstance() {
		if (instance == null) {
			instance = new SAT4JRef();
		}
		return instance;
	}

	@Override
	public String id() {
		return "sat4j";
	}
	@Override
	public boolean incremental() {
		return true;
	}

	@Override
	public Optional<String> getDescription() {
		return Optional.of("SAT4J is a Java library used for solving Boolean Satisfiability (SAT) problems and more generally Pseudo-Boolean (PB) problems. It is an open-source project under the GNU LGPL license, providing various SAT and MaxSAT solvers in Java. It is very reliable and works on all platforms");
	}

	@Override
	public SATSolver createSolver() {
		return new SAT4J(SolverFactory.instance().defaultSolver());
	}
	@Override
	public String type() {
		return "java";
	}

}
