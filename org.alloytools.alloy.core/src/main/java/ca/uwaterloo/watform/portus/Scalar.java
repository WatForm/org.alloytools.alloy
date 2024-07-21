package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.ErrorFatal;
import fortress.msfol.Term;

import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

/**
 * Represents a scalar or a function of scalars, including its guard.
 * True scalars are represented by nilary functions of scalars.
 * We assume that function composition is done by Alloy join: if f and g are functions of scalars, we assume that
 * f.g represents the function g o f.
 * (Notably, this precludes representing an Alloy function f : A->one B->C as a function f(a,c) -> b.)
 */
final class Scalar {

    private final int arity;

    private final Function<List<AnnotatedTerm>, AnnotatedTerm> scalarGenerator;
    private final Function<List<AnnotatedTerm>, BoolTerm> guardGenerator;

    public Scalar(int arity, Function<List<AnnotatedTerm>, AnnotatedTerm> scalarGenerator,
                  Function<List<AnnotatedTerm>, BoolTerm> guardGenerator) {
        this.arity = arity;
        this.scalarGenerator = scalarGenerator;
        this.guardGenerator = guardGenerator;
    }

    /** Create a nilary scalar. */
    public Scalar(AnnotatedTerm scalar, BoolTerm guard) {
        this(0, args -> scalar, args -> guard);
    }

    public int arity() {
        return arity;
    }

    public boolean isNilary() {
        return arity == 0;
    }

    public AnnotatedTerm getScalar(List<AnnotatedTerm> args) {
        if (args.size() != arity) {
            throw new ErrorFatal("Internal Portus error: getScalar expected " + arity + " args, got " + args.size());
        }
        return scalarGenerator.apply(args);
    }

    public AnnotatedTerm getScalar(AnnotatedTerm... args) {
        return getScalar(Arrays.asList(args));
    }

    public BoolTerm getGuard(List<AnnotatedTerm> args) {
        if (args.size() != arity) {
            throw new ErrorFatal("Internal Portus error: getGuard expected " + arity + " args, got " + args.size());
        }
        return guardGenerator.apply(args);
    }

    public BoolTerm getGuard(AnnotatedTerm... args) {
        return getGuard(Arrays.asList(args));
    }

    /**
     * Compose two scalars together. Given scalars f and g, compute g o f.
     * Specifically, given f : x1, ..., xn |-> f(x1, ..., xn) and g : y1, ..., ym |-> g(y1, ..., ym), compute
     *      g o f : x1, ..., xn, y2, ..., ym |-> g(f(x1, ..., xn), y2, ..., ym).
     * If g is nilary, throw an error.
     * Other combinations are theoretically possible, but this corresponds to the Alloy join f.g.
     */
    public static Scalar compose(Scalar f, Scalar g) {
        if (g.isNilary()) {
            throw new ErrorFatal("Cannot compose scalars (g o f) where g is nilary!");
        }

        int arity = f.arity() + g.arity() - 1;
        Function<List<AnnotatedTerm>, AnnotatedTerm> scalarGenerator = args -> {
            // g(f(x1, ..., xn), y2, ..., ym)
            List<AnnotatedTerm> fArgs = args.subList(0, f.arity());
            AnnotatedTerm fResult = f.getScalar(fArgs);
            List<AnnotatedTerm> gArgs = SetOps.concatenate(fResult, args.subList(f.arity(), arity));
            return g.getScalar(gArgs);
        };
        Function<List<AnnotatedTerm>, BoolTerm> guardGenerator = args -> {
            // guard_f(x1, ..., xn) && guard_g(f(x1, ..., xn), y2, ..., ym)
            List<AnnotatedTerm> fArgs = args.subList(0, f.arity());
            AnnotatedTerm fResult = f.getScalar(fArgs);
            List<AnnotatedTerm> gArgs = SetOps.concatenate(fResult, args.subList(f.arity(), arity));
            return new BoolTerm(Term.mkAnd(f.getGuard(fArgs).getTerm(), g.getGuard(gArgs).getTerm()));
        };
        return new Scalar(arity, scalarGenerator, guardGenerator);
    }

}
