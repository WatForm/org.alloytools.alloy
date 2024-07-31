package ca.uwaterloo.watform.portus;

import fortress.data.IntSuffixNameGenerator;
import fortress.data.NameGenerator;
import scala.collection.Set$;

/**
 * A decorator for a NameGenerator that sanitizes names so that Fortress can accept them.
 * The character " is permitted in Alloy identifiers but not Fortress identifiers, so it is replaced before being passed
 * to the wrapped NameGenerator.
 * TODO: Reverse the sanitization for display?
 */
public class SanitizingNameGenerator implements NameGenerator {

    private final NameGenerator delegate;

    public SanitizingNameGenerator(NameGenerator delegate) {
        this.delegate = delegate;
    }

    public SanitizingNameGenerator() {
        //noinspection unchecked
        this(new IntSuffixNameGenerator((scala.collection.immutable.Set<String>) Set$.MODULE$.empty(), 0));
    }

    private String sanitize(String name) {
        return name.replace("\"", "_Q");
    }

    @Override
    public String freshName(String base) {
        return delegate.freshName(sanitize(base));
    }

    @Override
    public void forbidName(String name) {
        delegate.forbidName(sanitize(name));
    }

}
