package ca.uwaterloo.watform.portus;

import fortress.data.NameGenerator;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class SanitizingNameGeneratorTest {

    @Test
    public void testEliminatesQuote() {
        NameGenerator nameGenerator = new SanitizingNameGenerator();
        assertEquals("x_Q_0", nameGenerator.freshName("x\""));
    }

    @Test
    public void testForbidUsesQuote() {
        NameGenerator nameGenerator = new SanitizingNameGenerator();
        nameGenerator.forbidName("x\"_0");
        assertEquals("x_Q_1", nameGenerator.freshName("x\""));
    }

}
