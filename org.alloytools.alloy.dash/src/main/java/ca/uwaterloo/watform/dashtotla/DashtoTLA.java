package ca.uwaterloo.watform.dashtotla;



import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashRef;

public class DashtoTLA 
{
    public static String translate(DashModule d)
    {
        if(!d.hasRoot())
        {
            System.out.println("Error - no root state, nothing to translate");
            return "";
        }

        StringBuilder translation = new StringBuilder("\nEXTENDS Integers, FiniteSets");
        translation.append("\nVARIABLE conf, events");
        translation.append(boilerplateLeafStates(d));
        translation.append(boilerplateAllStates(d));
        translation.append(events(d));
        translation.append(transitions(d));
        translation.append(Init(d));
        
        return translation.toString();
    }
    public static String resolveName(String s)
    {
        char SP = '_';
        return SP+s.replace('/', SP);
    }
    public static String boilerplateLeafStates(DashModule d)
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
    public static String isInState(String state)
    {
        return "_in"+resolveName(state);
    }
    public static String boilerplateAllStates(DashModule d)
    {
        List<String> states = d.getAllStateNames();
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
    public static String events(DashModule d)
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
            List<String> ENTER = toStringList(d.entered(s));
            List<String> EXIT = toStringList(d.exited(s));
            
            List<String> EXITresolved = new ArrayList<>();
            List<String> ENTERresolved = new ArrayList<>();
            for(String st : ENTER)ENTERresolved.add(resolveName(st));
            for(String st : EXIT)EXITresolved.add(resolveName(st));
            
            // System.out.println("\nTransition:"+s);
            // System.out.println("Entered:");
            // for(String st : ENTER)System.out.print("|"+st);
            // System.out.println("\nExited:");
            // for(String st : EXIT)System.out.print("|"+st);

            String srcState = d.getTransSrc(s).toString();
            String ON = "";
            String SEND  = "";
            try
            {
                ON = resolveName(d.getTransOn(s).getName());
                SEND = resolveName(d.getTransSend(s).getName());
            }
            catch(NullPointerException e){}
            ts.append("\n"+resolveName(s)+" == "+
                        "\n\t/\\"+isInState(srcState)+
                        "\n\t/\\ conf' = (conf \\ "+toSetOfStates(EXITresolved)+" ) \\union "+toSetOfStates(ENTERresolved)+
                        "\n\t/\\ {"+ON+"} \\subseteq events"+
                        "\n\t/\\ events' = (events / {"+ON+"}) \\union {"+SEND+"}");
        }
        System.out.println();

        ts.append("\n\nNext == ");
        for(String s : tranList)
        {
            ts.append("\n\t/\\ "+resolveName(s));
        }

        return ts.toString();
    }
    public static String Init(DashModule d)
    {
        StringBuilder init = new StringBuilder("\n\nInit == events = {}_/\\");
        List<String> defaultsOfRoot = d.getDefaults(d.getRootName());
        for(String s : defaultsOfRoot)init.append("\n\t\t\\/ "+isInState(s));
        return init.toString();
    }
    public static List<String> toStringList(List<DashRef> dfs)
    {
        List<String> ls = new ArrayList<>();
        for(DashRef df : dfs)ls.add(df.getName());
        return ls;
    }
    public static List<DashRef> toStateDashRefList(List<String> ls)
    {
        List<DashRef> dfs = new ArrayList<>();
        for(String s : ls)dfs.add(DashRef.createStateDashRef(s, null));
        return dfs;
    }
    public static List<DashRef> toTransitionDashRefList(List<String> ls)
    {
        List<DashRef> dfs = new ArrayList<>();
        for(String s : ls)dfs.add(DashRef.createTransDashRef(s, null));
        return dfs;
    }
    public static String toSetOfStates(List<String> states)
    {
        StringBuilder sb = new StringBuilder("{");
        for(int i=0;i<states.size();i++)
        {
            sb.append(states.get(i)+(i==states.size()-1?"":","));
        }
        sb.append("}");
        return sb.toString();
    }
}
