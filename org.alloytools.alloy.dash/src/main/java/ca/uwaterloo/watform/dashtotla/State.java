package ca.uwaterloo.watform.dashtotla;

import java.util.List;
import java.util.ArrayList;

import ca.uwaterloo.watform.parser.DashModule;

public class State 
{
    public static String isInState(String state) // used to check if one is in a non-leaf state
    {
        return Util.resolveName("in__"+state);
    }
    public static String createInStates(DashModule d) // formulae to determine if one is present in a state
    {
        List<String> states = Util.topoSortStates(d);
        
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment(" in states"));
        for(String s : states)
        {
            code.append("\n"+isInState(s)+" "+TLA.DEFINE+" ");
            if(d.isLeaf(s))
            {
                String resolved = Util.resolveName(s);
                code.append(resolved+" \\in "+Variable.CONF);
                continue;
            }

            // dealing with non-leaf states
            List<String> children = d.getImmChildren(s);
            List<String> andChildren = new ArrayList<>(); //concurrency

            for(String ch : children)
                if(d.isAnd(ch))
                    andChildren.add(ch);
                else
                    code.append("\n\t"+TLA.OR+" "+isInState(ch)); // can be in any "or" child
            
            // if is in one "and" child, must be in all "and" children
            if(andChildren.size()==0)
                continue;
            code.append("\n\t"+TLA.OR);
            for(String ch : andChildren)
                code.append("\n\t\t"+TLA.AND+" "+isInState(ch));

        }
        return code.toString();
    }
}
