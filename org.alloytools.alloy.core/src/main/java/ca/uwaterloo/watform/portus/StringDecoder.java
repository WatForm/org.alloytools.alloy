package ca.uwaterloo.watform.portus;

import fortress.msfol.DomainElement;

/**
 * A StringDecoder can decode a domain element representing a string constant to the string constant being represented.
 * This is an interface to decouple this functionality from its implementation together with the rest of the
 * functionality in StringTranslator.
 */
interface StringDecoder {

    /**
     * Decode the domain element to the string constant it represents, or return null if it does not represent a string
     * constant.
     */
    String decode(DomainElement de);

}
