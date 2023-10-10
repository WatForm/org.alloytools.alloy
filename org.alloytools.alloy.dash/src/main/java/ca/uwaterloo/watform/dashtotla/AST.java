package ca.uwaterloo.watform.dashtotla;

import de.uka.ilkd.pp.DataLayouter;
import de.uka.ilkd.pp.NoExceptions;
import de.uka.ilkd.pp.StringBackend;

public class AST
{
    public String node;
    public AST left;
    public AST right;   
    public static String singleton(String set) // the constraints that sets the cardinality of this set to 1
    {
        return TLA.parenthesis(TLA.FOR_ALL+" x,y "+TLA.IN+" "+set+" "+TLA.PREDICATE_SCOPE+" x=y ");
    }
    public String print()
    {
        StringBuilder code = new StringBuilder("");
        return code.toString();
    }
}