package ca.uwaterloo.watform.dashtotla;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashModule;

public class StandardFormulae 
{
    // boilerplate formulae, shared by all functions
    public static final String INIT = "Init";
    public static final String NEXT = "Next";
    public static final String TYPE_OK = "TypeOK";
    
    public static final String STUTTER = "_stutter";

    public static String Next(DashModule d) // Next formula in TLA+
    {
        List<String> tranList = d.getAllTransNames();
        StringBuilder next = new StringBuilder("\n\n"+NEXT+" "+TLA.DEFINE+" "+STUTTER);
        for(String s : tranList)
        {
            next.append("\n\t"+TLA.OR+" "+Util.resolveName(s));
        }
        return next.toString();
    }
    public static String TypeOK(DashModule d) // TLA+'s technique to ensure that types are appropriate
    {
        String variables[] = new String[]{Variable.CONF, Variable.INTERNAL_EVENTS, Variable.ENVIRONMENTAL_EVENTS, Variable.SCOPES_USED};
        
        StringBuilder code = new StringBuilder("\n\n"+TLA.comment("type-checking")+"\n"+TYPE_OK+" "+TLA.DEFINE+" ");
        for(String s : variables)
            code.append("\n\t"+TLA.AND+" "+s+" "+TLA.SUBSET+" "+Variable.superset(s));

        return code.toString();
    }
    public static String Init(DashModule d, boolean singleEnvInput) // Init formula in TLA+
    {
        StringBuilder init = new StringBuilder("\n\n"+INIT+" "+TLA.DEFINE+" ");

        List<String> variables = new ArrayList<>(); // both boilerplate and actual variables
        variables.add(Variable.CONF);
        variables.add(Variable.INTERNAL_EVENTS);
        variables.add(Variable.SCOPES_USED);
        variables.add(Variable.STABLE);

        for(String v : variables)
            init.append("\n\t"+TLA.AND+" "+v+TLA.EQUAL+Variable.initial(v));

        init.append("\n\t"+TLA.AND+" "+Variable.ENVIRONMENTAL_EVENTS+" "+TLA.SUBSET+" "+Variable.superset(Variable.ENVIRONMENTAL_EVENTS));
        if(singleEnvInput)
            init.append(" "+TLA.AND+AST.singleton(Variable.ENVIRONMENTAL_EVENTS));

        return init.toString();
    }

    // when no tranitions are enabled, the system stays in current state while waiting for an environmental event to be sent
    public static String Stutter(DashModule d, boolean singleEnvInput)
    {
        return  "\n\n"+STUTTER+" "+TLA.DEFINE+" "+TLA.NOT+Transition.EXISTS_ENABLED_TRANSITION+
                "\n\t"+TLA.AND+" "+Variable.prime(Variable.CONF)+TLA.EQUAL+Variable.CONF+
                "\n\t"+TLA.AND+" "+Variable.prime(Variable.INTERNAL_EVENTS)+TLA.EQUAL+Variable.INTERNAL_EVENTS+
                "\n\t"+TLA.AND+"\t"+TLA.OR+" "+Variable.prime(Variable.ENVIRONMENTAL_EVENTS)+TLA.EQUAL+Variable.ENVIRONMENTAL_EVENTS+
                "\n\t\t"+TLA.OR+" "+TLA.parenthesis(Variable.prime(Variable.ENVIRONMENTAL_EVENTS)+" "+TLA.SUBSET+" "+Variable.superset(Variable.ENVIRONMENTAL_EVENTS)+" "+
                (singleEnvInput?TLA.AND+" "+AST.singleton(Variable.ENVIRONMENTAL_EVENTS):""))+
                "\n\t"+TLA.AND+" "+Variable.prime(Variable.SCOPES_USED)+TLA.EQUAL+TLA.NULL_SET+
                "\n\t"+TLA.AND+" "+Variable.prime(Variable.STABLE)+TLA.EQUAL+TLA.TRUE;




    }
}
