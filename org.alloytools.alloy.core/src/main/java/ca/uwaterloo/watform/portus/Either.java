package ca.uwaterloo.watform.portus;

import java.util.Objects;

/**
 * A utility tagged union type. Stores two values, exactly one of which is non-null.
 * Invariant: hasFirst() XOR hasSecond().
 */
final class Either<A, B> {

    private final A first;
    private final B second;

    private Either(A first, B second) {
        this.first = first;
        this.second = second;
    }

    /**
     * Construct an Either with the element of the first type non-null.
     * @param first The content of the Either. Must be non-null.
     */
    public static <A, B> Either<A, B> asFirst(A first) {
        Objects.requireNonNull(first);
        return new Either<>(first, null);
    }

    /**
     * Construct an Either with the element of the second type non-null.
     * @param second The content of the Either. Must be non-null.
     */
    public static <A, B> Either<A, B> asSecond(B second) {
        Objects.requireNonNull(second);
        return new Either<>(null, second);
    }

    /** Return whether the contents of the Either is of the first type. */
    public boolean hasFirst() {
        return first != null;
    }

    /** Return whether the contents of the Either is of the second type. */
    public boolean hasSecond() {
        return second != null;
    }

    /**
     * Return the contents of the Either if it is of the first type, or null if the contents
     * are of the second type.
     */
    public A getFirst() {
        return first;
    }

    /**
     * Return the contents of the Either if it is of the second type, or null if the contents
     * are of the first type.
     */
    public B getSecond() {
        return second;
    }

    @Override
    public String toString() {
        return "Either[" + (hasFirst() ? "first=" + first : "second=" + second) + "]";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Either<?, ?> either = (Either<?, ?>) o;
        return Objects.equals(getFirst(), either.getFirst())
                && Objects.equals(getSecond(), either.getSecond());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getFirst(), getSecond());
    }

}
