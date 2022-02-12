package ca.uwaterloo.watform.portus;

import edu.mit.csail.sdg.alloy4.A4Reporter;

/**
 * The basic translator that provides unoptimized translations of every supported node.
 */
final class DefaultTranslator extends BaseTranslator {

    public DefaultTranslator(A4Reporter reporter, Translator topLevelTranslator) {
        super(reporter, topLevelTranslator);
    }

    // TODO - base translations of everything

}
