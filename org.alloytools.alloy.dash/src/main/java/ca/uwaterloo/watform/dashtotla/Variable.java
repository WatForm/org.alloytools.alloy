package ca.uwaterloo.watform.dashtotla;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashModule;

public class Variable 
{
    

    // boilerplate variables
    public static final String CONF = "_conf";
    public static final String INTERNAL_EVENTS = "_internal_events"; 
    public static final String ENVIRONMENTAL_EVENTS = "_environmental_events";
    public static final String SCOPES_USED = "_scopes_used";
    public static final String STABLE = "_stable";
    
    // variable in next step
    public static String prime(String variable){return variable+"'";} 

    // set holding every value which a variable can hold
    public static String superset(String variable){return variable+"__superset";} 

    // initial value of a variable
    public static String initial(String variable){return variable+"__initial";}

    public static String initialValues(DashModule d)
    {
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment(" initial values"));

        code.append("\n"+initial(Variable.CONF)+" "+TLA.DEFINE+" "+TLA.set(Util.resolveList(Util.toStringList(d.initialEntered()))));
        code.append("\n"+initial(Variable.ENVIRONMENTAL_EVENTS)+" "+TLA.DEFINE+" "+TLA.NULL_SET);
        code.append("\n"+initial(Variable.SCOPES_USED)+" "+TLA.DEFINE+" "+TLA.NULL_SET);
        code.append("\n"+initial(Variable.STABLE)+" "+TLA.DEFINE+" "+TLA.TRUE);

        return code.toString();
    }
    public static String declareVariables(DashModule d)
    {
        List<String> variables = new ArrayList<>();
        variables.add(SCOPES_USED);
        variables.add(CONF);
        variables.add(INTERNAL_EVENTS);
        variables.add(ENVIRONMENTAL_EVENTS);
        variables.add(STABLE);
        return "\n"+TLA.variables(variables);
    }
    public static String supersets(DashModule d) // define the set of all possible values for a variable's elements
    {
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment(" supersets"));

        // conf, scopes used
        List<String> resolvedStateNames = new ArrayList<>();
        List<String> resolvedBasicStateNames = new ArrayList<>();
        for(String s : d.getAllStateNames())
        {
            resolvedStateNames.add(Util.resolveName(s));
            if(d.isLeaf(s))
                resolvedBasicStateNames.add(Util.resolveName(s));
        }    
        code.append("\n"+superset(Variable.CONF)+" "+TLA.DEFINE+" "+TLA.set(resolvedBasicStateNames));
        code.append("\n"+superset(Variable.SCOPES_USED)+" "+TLA.DEFINE+" "+TLA.set(resolvedStateNames));

        // internal events
        List<String> resolvedInternalEventNames = new ArrayList<>();
        for(String s : d.getAllInternalEventNames())resolvedInternalEventNames.add(Util.resolveName(s));
        code.append("\n"+superset(Variable.INTERNAL_EVENTS)+" "+TLA.DEFINE+" "+TLA.set(resolvedInternalEventNames));

        // environmental events
        List<String> resolvedEnvironmentalEventNames = new ArrayList<>();
        for(String s : d.getAllEnvironmentalEventNames())resolvedEnvironmentalEventNames.add(Util.resolveName(s));
        code.append("\n"+superset(Variable.ENVIRONMENTAL_EVENTS)+" "+TLA.DEFINE+" "+TLA.set(resolvedEnvironmentalEventNames));
        

        return code.toString();
    }
}
