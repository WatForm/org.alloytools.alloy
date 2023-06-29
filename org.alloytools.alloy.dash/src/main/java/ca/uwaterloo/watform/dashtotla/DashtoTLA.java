package ca.uwaterloo.watform.dashtotla;



import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.*;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashRef;

public class DashtoTLA 
{
    public static String translate(DashModule d, String moduleName)
    {
        if(!d.hasRoot())
        {
            System.out.println("Error - no root state, nothing to translate");
            return "\\* Error - no root state, nothing to translate";
        }

        String header = "------------------------------- MODULE "+moduleName+" -------------------------------";
        String Extends = "\nEXTENDS Integers, FiniteSets";
        String variables = "\nVARIABLE conf, events";
        StringBuilder translation = new StringBuilder("");
        translation.append(boilerplateLeafStates(d));
        translation.append(boilerplateAllStates(d));
        translation.append(boilerplateInternalEvents(d));
        translation.append(transitions(d));
        translation.append(Init(d));
        translation.append(Next(d));
        String footer = "\n=============================================================================";
        String comment = "\\* Modification History\n\\* Translated from Dash at "+System.currentTimeMillis()+" EPOCH";
        
        return header+Extends+variables+translation.toString()+footer+comment;
    }
    public static String resolveName(String s) // get rid of unsupported characters in full names
    {
        char SP = '_';
        return SP+s.replace('/', SP);
    }
    public static String boilerplateLeafStates(DashModule d) // atoms for each leaf state
    {
        List<String> states = d.getAllStateNames();
        StringBuilder leafStates = new StringBuilder("");
        int ct=0;
        for(int i =0; i<states.size();i++)
        {
            String s = states.get(i);
            if(d.isLeaf(s))leafStates.append("\n"+resolveName(s)+"=="+ct++);
        }
        return "\n\n\\* basic states"+leafStates;
    }
    private static String isInState(String state)
    {
        return "_in"+resolveName(state);
    }
    public static String boilerplateAllStates(DashModule d)
    {
        List<String> states = topoSortStates(d);
        StringBuilder code = new StringBuilder("\n\n\\* in states");
        for(String s : states)
        {
            code.append("\n"+isInState(s)+" == ");
            if(d.isLeaf(s))
            {
                code.append(resolveName(s)+" \\in conf");
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
    public static String transitions(DashModule d)
    {
        // assumption - guard is tautology
        StringBuilder ts = new StringBuilder("\n\n\\* transitions");
        List<String> tranList = d.getAllTransNames();
        for(String s : tranList)
        {
            // formula for conf
            String srcState = d.getTransSrc(s).toString();
            String CONF = "\n\t/\\"+isInState(srcState);

            // formula for conf' //t his a test of scr
            List<String> ENTER = toStringList(d.entered(s));
            List<String> EXIT = toStringList(d.exited(s));
            List<String> EXITresolved = new ArrayList<>();
            List<String> ENTERresolved = new ArrayList<>();
            ENTER.forEach(st -> ENTERresolved.add(resolveName(st)));
            EXIT.forEach(st -> EXITresolved.add(resolveName(st)));
            String CONF_ = "\n\t/\\ conf' = (conf \\ "+toSetOfStates(EXITresolved)+" ) \\union "+toSetOfStates(ENTERresolved);
        
            DashRef ON = d.getTransOn(s);
            DashRef SEND = d.getTransSend(s);

            // formula for events
            String EVENTS = "";
            if(ON!=null)EVENTS = "\n\t/\\ {"+resolveName(ON.getName())+"} \\subseteq events";

            // formula for events'
            String E = "events";
            if(ON!=null) E = "("+E+" \\ {"+resolveName(ON.getName())+"})"; // remove consumed events
            if(SEND!=null) E += " \\union {"+resolveName(SEND.getName())+"}"; // add generated events
            String EVENTS_ = "\n\t/\\ events' = "+E;

            ts.append("\n"+resolveName(s)+" == "+CONF+CONF_+EVENTS+EVENTS_);
        }
        return ts.toString();
    }
    public static String Next(DashModule d) // Next formula in TLA+
    {
        List<String> tranList = d.getAllTransNames();
        StringBuilder next = new StringBuilder("\n\nNext == ");
        for(String s : tranList)
        {
            next.append("\n\t/\\ "+resolveName(s));
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
