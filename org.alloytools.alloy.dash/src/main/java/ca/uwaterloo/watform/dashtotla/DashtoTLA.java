package ca.uwaterloo.watform.dashtotla;



import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
//import java.util.function.*;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashRef;

public class DashtoTLA 
{
    // boilerplate formulae, shared by all functions
    public static final String INIT = "Init";
    public static final String NEXT = "Next";
    public static final String TYPE_OK = "TypeOK";
    public static final String EXISTS_ENABLED_TRANSITION = "_exists_enabled_tranistions";
    public static final String STUTTER = "_stutter";

    // boilerplate variables
    public static final String CONF = "_conf";
    public static final String INTERNAL_EVENTS = "_internal_events"; 
    public static final String ENVIRONMENTAL_EVENTS = "_environmental_events";
    
    // variable in next step
    public static String prime(String variable){return variable+"'";} 

    // set holding every value which a variable can hold
    public static String superset(String variable){return variable+"__superset";} 

    // initial value of a variable
    public static String initial(String variable){return variable+"__initial";}

    public static String translate(DashModule d, String moduleName)
    {
        if(!d.hasRoot())
        {
            System.out.println("Error - no root state, nothing to translate");
            return "\\* Error - no root state, nothing to translate";
        }

        String header = "------------------------------- MODULE "+moduleName+" -------------------------------";
        String Extends = "\nEXTENDS Integers, FiniteSets";
        String variables = "\nVARIABLE "+CONF+", "+INTERNAL_EVENTS+", "+ENVIRONMENTAL_EVENTS;
        StringBuilder translation = new StringBuilder("");
        translation.append(atomsLeafStates(d));
        translation.append(atomsInternalEvents(d));
        translation.append(atomsEnvironmentalEvents(d));
        translation.append(supersets(d));
        translation.append(initialValues(d));
        translation.append(TypeOK(d));
        translation.append(createAllStates(d));
        translation.append(transitions(d));
        translation.append(Init(d));
        translation.append(Stutter(d));
        translation.append(Next(d));
        String footer = "\n=============================================================================";
        String comment =    "\n\\* Modification History"+
                            "\n\\* Translated from Dash at "+System.currentTimeMillis()+" EPOCH";
        
        return header+Extends+variables+translation.toString()+footer+comment;
    }
    public static String resolveName(String s) // get rid of unsupported characters in full names
    {
        char SP = '_';  // SP is a specual character that cannot appear in any variablename in dash, but can in TLA+
        return SP+s.replace('/', SP);
    }
    public static String atomsLeafStates(DashModule d) // atoms for each leaf state
    {
        List<String> states = d.getAllStateNames();
        StringBuilder leafStates = new StringBuilder("\n\n\\* basic states");
        
        for(String s : states)
            if(d.isLeaf(s))        
                leafStates.append("\n"+resolveName(s)+" == \""+resolveName(s)+"\"");
                
        return leafStates.toString();
    }
    private static String isInState(String state) // used to check if one is in a non-leaf state
    {
        return resolveName("in__"+state);
    }
    public static String supersets(DashModule d) // define the set of all possible values for a variable's elements
    {
        StringBuilder code = new StringBuilder("\n\n\\* supersets");

        // conf
        List<String> resolvedStateNames = new ArrayList<>();
        for(String s : d.getAllStateNames())
            if(d.isLeaf(s))
                resolvedStateNames.add(resolveName(s));
        code.append("\n"+superset(CONF)+" == "+toSet(resolvedStateNames));

        // internal events
        List<String> resolvedInternalEventNames = new ArrayList<>();
        for(String s : d.getAllInternalEventNames())resolvedInternalEventNames.add(resolveName(s));
        code.append("\n"+superset(INTERNAL_EVENTS)+" == "+toSet(resolvedInternalEventNames));

        // environmental events
        List<String> resolvedEnvironmentalEventNames = new ArrayList<>();
        for(String s : d.getAllEnvironmentalEventNames())resolvedEnvironmentalEventNames.add(resolveName(s));
        code.append("\n"+superset(ENVIRONMENTAL_EVENTS)+" == "+toSet(resolvedEnvironmentalEventNames));
        
        return code.toString();
    }
    public static String createAllStates(DashModule d) // formulae to determine if one is present in a state
    {
        List<String> states = topoSortStates(d);
        
        StringBuilder code = new StringBuilder("\n\n\\* in states");
        for(String s : states)
        {
            code.append("\n"+isInState(s)+" == ");
            if(d.isLeaf(s))
            {
                String resolved = resolveName(s);
                code.append(resolved+" \\in "+CONF);
                continue;
            }

            // dealing with non-leaf states
            List<String> children = d.getImmChildren(s);
            for(String ch : children)
                code.append("\n\t\\/ "+isInState(ch));

        }
        return code.toString();
    }
    public static String atomsInternalEvents(DashModule d) // atoms for each internal event in TLA+
    {
        StringBuilder code = new StringBuilder("\n\n\\* internal events");
        List<String> events = d.getAllInternalEventNames();
        for(String ev : events)
            code.append("\n"+resolveName(ev)+" == \""+resolveName(ev)+"\"");
        return code.toString();
    }
    public static String atomsEnvironmentalEvents(DashModule d) // atoms for each internal event in TLA+
    {
        StringBuilder code = new StringBuilder("\n\n\\* environmental events");
        List<String> events = d.getAllEnvironmentalEventNames();
        for(String ev : events)
            code.append("\n"+resolveName(ev)+" == \""+resolveName(ev)+"\"");
        return code.toString();
    }
    public static String postCondition(DashModule d, String trans)
    {
        StringBuilder code = new StringBuilder("");

        // conf'
        List<String> entered = toStringList(d.entered(trans));
        List<String> exited = toStringList(d.exited(trans));
        String confPrimed = "\n\t/\\ "+prime(CONF)+" = ("+CONF+" \\ "+toSetResolved(exited)+" ) \\union "+toSetResolved(entered);
        
        // events'
        DashRef on = d.getTransOn(trans);
        DashRef send = d.getTransSend(trans);
        String E = INTERNAL_EVENTS;
        if(on!=null) E = "("+E+" \\ {"+resolveName(on.getName())+"})"; // remove consumed events
        if(send!=null) E += " \\union {"+resolveName(send.getName())+"}"; // add generated events
        String eventsPrimed = "\n\t/\\ "+prime(INTERNAL_EVENTS)+" = "+E;

        code.append(confPrimed);
        code.append(eventsPrimed);
        return code.toString();
    }
    public static String preCondition(DashModule d, String trans)
    {
        StringBuilder code = new StringBuilder("");

        // conf
        String srcState = d.getTransSrc(trans).toString();
        String CONF = "\n\t/\\ "+isInState(srcState);

        // formula for events
        DashRef ON = d.getTransOn(trans);
        String EVENTS = "";
        if(ON!=null)EVENTS = "\n\t/\\ {"+resolveName(ON.getName())+"} \\subseteq "+INTERNAL_EVENTS;

        code.append(CONF);
        code.append(EVENTS);
        return code.toString();
    }
    public static String transitions(DashModule d)
    {
        // assumption - guard is tautology
        StringBuilder ts = new StringBuilder("\n\n\\* transitions");
        List<String> tranList = d.getAllTransNames();
        List<String> preCondList = new ArrayList<>();
        for(String s : tranList)
        {
            String preConditionName = "_pre__"+resolveName(s);
            String postConditionName = "_post__"+resolveName(s);
            ts.append("\n\n"+preConditionName+" == "+preCondition(d, s));
            ts.append("\n"+postConditionName+" == "+postCondition(d, s));
            ts.append("\n"+resolveName(s)+" == "+preConditionName+" /\\ "+postConditionName);
            preCondList.add(preConditionName);
        }

        StringBuilder somePrecond = new StringBuilder("\n\n"+EXISTS_ENABLED_TRANSITION+" == ");
        for(String s : preCondList)
            somePrecond.append("\n\t/\\ "+s);

        return ts.append(somePrecond).toString();
    }
    // when no tranitions are enabled, the system stays in current state while waiting for an environmental event to be sent
    public static String Stutter(DashModule d)
    {
        return  "\n\n"+STUTTER+" == ~"+EXISTS_ENABLED_TRANSITION+
                "\n\t/\\ "+prime(CONF)+" = "+CONF+
                "\n\t/\\ "+prime(INTERNAL_EVENTS)+" = "+INTERNAL_EVENTS;

    }
    public static String Next(DashModule d) // Next formula in TLA+
    {
        List<String> tranList = d.getAllTransNames();
        StringBuilder next = new StringBuilder("\n\n"+NEXT+" == "+STUTTER);
        for(String s : tranList)
        {
            next.append("\n\t\\/ "+resolveName(s));
        }
        return next.toString();
    }
    public static String TypeOK(DashModule d) // TLA+'s technique to ensure that types are appropriate
    {
        String variables[] = new String[]{CONF, INTERNAL_EVENTS, ENVIRONMENTAL_EVENTS};
        
        StringBuilder code = new StringBuilder("\n\n\\* type-checking\n"+TYPE_OK+" == ");
        for(String s : variables)
            code.append("\n\t/\\ "+s+" \\subseteq "+superset(s));

        return code.toString();
    }
    public static String Init(DashModule d) // Init formula in TLA+
    {
        StringBuilder init = new StringBuilder("\n\n"+INIT+" == ");

        init.append("\n\t/\\ "+INTERNAL_EVENTS+" = {}");
        init.append("\n\t/\\ "+ENVIRONMENTAL_EVENTS+" = {}");
        init.append("\n\t/\\ "+CONF+" = "+toSetResolved(toStringList(d.initialEntered())));

        return init.toString();
    }

    // util functions
    public static String toSet(List<String> elements) // set in TLA+ notation
    {
        StringBuilder sb = new StringBuilder("{");
        for(int i=0;i<elements.size()-1;i++) // all except last element has comma after it
        {
            sb.append(elements.get(i)+",");
        }
        if(elements.size()!=0)sb.append(elements.get(elements.size()-1)); // add last element
        sb.append("}");
        return sb.toString();
    }
    public static String toSetResolved(List<String> elements) // set of strings in TLA+ notation
    {
        StringBuilder sb = new StringBuilder("{");
        for(int i=0;i<elements.size()-1;i++) // all except last element has comma after it
        {
            sb.append(resolveName(elements.get(i))+",");
        }
        if(elements.size()!=0)sb.append(resolveName(elements.get(elements.size()-1))); // add last element
        sb.append("}");
        return sb.toString();
    }
    public static List<String> LeafDefaultsOf(DashModule d, String state)
    {
        List<String> states = d.getDefaults(state);
        int i = 0;
        while(i < states.size())
        {
            String s = states.get(i);
            if(d.isLeaf(s)) // skip over defaults if they are already leaf states
            {
                i++;
                continue;
            }
            // if state is AND, all children are added
            // if state is OR, only default child is added
            states.addAll(d.getDefaults(s)); 
            states.remove(i); // non-leaf state removed after its children are added
        }
        return states; // at this point, all elements of states are leaf states
    }
    public static List<String> topoSortStates(DashModule d) // each state occurs only after all its children occur
    {
        List<String> states = new ArrayList<>();
        states.add(d.getRootName());
        int i = 0;
        while(i < states.size())
        {
            List<String> children = d.getImmChildren(states.get(i));
            i++;
            for(String ch : children)states.add(ch);
        }
        Collections.reverse(states);
        return states;
    }
    public static List<String> toStringList(List<DashRef> dfs)
    {
        List<String> ls = new ArrayList<>();
        for(DashRef df : dfs)ls.add(df.getName());
        return ls;
    }
    /* 
    public static List<DashRef> toDashRefList(List<String> ls, Function<String, DashRef> createDashRef) 
    {
    List<DashRef> dfs = new ArrayList<>();
    for (String s : ls) {
        dfs.add(createDashRef.apply(s));
    }
    return dfs;
    }
    */
}