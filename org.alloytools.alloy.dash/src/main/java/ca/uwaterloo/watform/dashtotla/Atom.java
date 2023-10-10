package ca.uwaterloo.watform.dashtotla;

import java.util.List;

import ca.uwaterloo.watform.parser.DashModule;


public class Atom 
{
    public static String leafStates(DashModule d) // atoms for each leaf state
    {
        List<String> states = d.getAllStateNames();
        StringBuilder leafStates = new StringBuilder("\n\n"+TLA.comment("basic states"));
        
        for(String s : states)
            if(d.isLeaf(s))        
                leafStates.append("\n"+Util.resolveName(s)+" "+TLA.DEFINE+" "+TLA.string(Util.resolveName(s)));
                
        return leafStates.toString();
    }
    public static String nonLeafStates(DashModule d) // atoms for each leaf state
    {
        List<String> states = d.getAllStateNames();
        StringBuilder leafStates = new StringBuilder("\n\n"+TLA.comment(" non-basic states"));
        
        for(String s : states)
            if(!d.isLeaf(s))        
                leafStates.append("\n"+Util.resolveName(s)+" "+TLA.DEFINE+" "+TLA.string(Util.resolveName(s)));
                
        return leafStates.toString();
    }
    public static String internalEvents(DashModule d) // atoms for each internal event in TLA+
    {
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment(" internal events"));
        List<String> events = d.getAllInternalEventNames();
        for(String ev : events)
            code.append("\n"+Util.resolveName(ev)+" "+TLA.DEFINE+" "+TLA.string(Util.resolveName(ev)));
        return code.toString();
    }
    public static String environmentalEvents(DashModule d) // atoms for each internal event in TLA+
    {
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment(" environmental events"));
        List<String> events = d.getAllEnvironmentalEventNames();
        for(String ev : events)
            code.append("\n"+Util.resolveName(ev)+" "+TLA.DEFINE+" "+TLA.string(Util.resolveName(ev)));
        return code.toString();
    }
}
