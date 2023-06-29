package ca.uwaterloo.watform.dashtotla;



import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
//import java.util.function.*;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashRef;

public class DashtoTLA 
{
    // common formulae shared by all functions
    public static final String INIT = "Init";
    public static final String NEXT = "Next";
    public static final String TYPE_OK = "TypeOK";
    public static final String EXISTS_ENABLED_TRANSITION = "_exists_enabled_tranistions";
    public static final String STUTTER = "stutter";
    public static final String CONF = "conf";
    public static final String EVENTS = "events";

    //public static final String  = "";
    public static String translate(DashModule d, String moduleName)
    {
        if(!d.hasRoot())
        {
            System.out.println("Error - no root state, nothing to translate");
            return "\\* Error - no root state, nothing to translate";
        }

        String header = "------------------------------- MODULE "+moduleName+" -------------------------------";
        String Extends = "\nEXTENDS Integers, FiniteSets";
        String variables = "\nVARIABLE "+CONF+", "+EVENTS;
        StringBuilder translation = new StringBuilder("");
        translation.append(createLeafStates(d));
        translation.append(createAllStates(d));
        translation.append(boilerplateInternalEvents(d));
        translation.append(transitions(d));
        translation.append(Init(d));
        translation.append(Next(d));
        String footer = "\n=============================================================================";
        String comment = "\n\\* Modification History\n\\* Translated from Dash at "+System.currentTimeMillis()+" EPOCH";
        
        return header+Extends+variables+translation.toString()+footer+comment;
    }
    public static String resolveName(String s) // get rid of unsupported characters in full names
    {
        char SP = '_';
        return SP+s.replace('/', SP);
    }
    public static String createLeafStates(DashModule d) // atoms for each leaf state
    {
        List<String> states = d.getAllStateNames();
        StringBuilder leafStates = new StringBuilder("");
        
        for(String s : states)
            if(d.isLeaf(s))
                leafStates.append("\n"+resolveName(s)+" == \""+s+"\"");
            
        return "\n\n\\* basic states"+leafStates;
    }
    private static String isInState(String state)
    {
        return resolveName("in__"+state);
    }
    public static String createAllStates(DashModule d)
    {
        List<String> states = topoSortStates(d);
        StringBuilder code = new StringBuilder("\n\n\\* in states");
        for(String s : states)
        {
            code.append("\n"+isInState(s)+" == ");
            if(d.isLeaf(s))
            {
                code.append(resolveName(s)+" \\in "+CONF);
                continue;
            }

            // dealing with non-leaf states
            List<String> children = d.getImmChildren(s);
            for(String ch : children)
                code.append("\n\t\\/ "+isInState(ch));

        }
        return code.toString();
    }
    public static String boilerplateInternalEvents(DashModule d) // atoms for each internal event in TLA+
    {
        StringBuilder code = new StringBuilder("\n\n\\* events");
        List<String> events = d.getAllInternalEventNames();
        int ct = 0;
        for(String ev : events)
            code.append("\n"+resolveName(ev)+" == "+(ct++));
        return code.toString();
    }
    public static String postCondition(DashModule d, String trans)
    {
        StringBuilder code = new StringBuilder("");

        // conf'
        List<String> entered = toStringList(d.entered(trans));
        List<String> exited = toStringList(d.exited(trans));
        List<String> exitedResolved = new ArrayList<>();
        List<String> enteredResolved = new ArrayList<>();
        entered.forEach(st -> enteredResolved.add(resolveName(st)));
        exited.forEach(st -> exitedResolved.add(resolveName(st)));
        String confPrimed = "\n\t/\\ "+CONF+"' = ("+CONF+" \\ "+toSetOfStates(exitedResolved)+" ) \\union "+toSetOfStates(enteredResolved);
        
        // events'
        DashRef on = d.getTransOn(trans);
        DashRef send = d.getTransSend(trans);
        String E = "events";
        if(on!=null) E = "("+E+" \\ {"+resolveName(on.getName())+"})"; // remove consumed events
        if(send!=null) E += " \\union {"+resolveName(send.getName())+"}"; // add generated events
        String eventsPrimed = "\n\t/\\ events' = "+E;

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
        if(ON!=null)EVENTS = "\n\t/\\ {"+resolveName(ON.getName())+"} \\subseteq events";

        code.append(CONF);
        code.append(EVENTS);
        return code.toString();
    }
    public static String transitions(DashModule d)
    {
        // assumption - guard is tautology
        StringBuilder ts = new StringBuilder("\n\n\\* transitions");
        List<String> tranList = d.getAllTransNames();
        for(String s : tranList)
        {
            String preConditionName = "_pre__"+resolveName(s);
            String postConditionName = "_post__"+resolveName(s);
            ts.append("\n\n"+preConditionName+" == "+preCondition(d, s));
            ts.append("\n"+postConditionName+" == "+postCondition(d, s));
            ts.append("\n"+resolveName(s)+" == "+preConditionName+" /\\ "+postConditionName);
        }
        return ts.toString();
    }
    public static String Next(DashModule d) // Next formula in TLA+
    {
        List<String> tranList = d.getAllTransNames();
        StringBuilder next = new StringBuilder("\n\nNext == ");
        for(String s : tranList)
        {
            next.append("\n\t\\/ "+resolveName(s));
        }
        return next.toString();
    }
    public static String Init(DashModule d) // Init formula in TLA+
    {
        StringBuilder init = new StringBuilder("\n\nInit == events = {} /\\");
        List<String> defaultsOfRoot = d.getDefaults(d.getRootName());
        for(String s : defaultsOfRoot)init.append("\n\t\t\\/ "+isInState(s));
        return init.toString();
    }
    public static String toSetOfStates(List<String> states) // set in TLA+ notation
    {
        StringBuilder sb = new StringBuilder("{");
        for(int i=0;i<states.size()-1;i++) // all except last element has comma after it
        {
            sb.append(states.get(i)+",");
        }
        sb.append(states.get(states.size()-1)); // add last element
        sb.append("}");
        return sb.toString();
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

    // util functions to switch between DashRef and String
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