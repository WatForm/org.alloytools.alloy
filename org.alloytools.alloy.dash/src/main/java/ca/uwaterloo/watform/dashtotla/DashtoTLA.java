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
        translation.append("\nVARIABLE conf");
        translation.append(boilerplateBasicStates(d));
        translation.append(transitions(d));
        translation.append(Init(d));
        
        return translation.toString();
    }
    public static String resolveName(String s)
    {
        return s.replace("/", "_");
    }
    public static String boilerplateBasicStates(DashModule d)
    {
        List<String> states = d.getAllStateNames();
        StringBuilder basicStates = new StringBuilder("");
        for(int i =0; i<states.size();i++)
            {
                String s = states.get(i);
                if(d.isLeaf(s))basicStates.append("\n"+resolveName(s)+"=="+i);
            }
        return "\n\n\\* basic states"+basicStates;
    }
    public static String transitions(DashModule d)
    {
        // assumption - trigger and guard are tautologies
        StringBuilder ts = new StringBuilder("\n\n\\* transitions");
        List<String> tranList = d.getAllTransNames();
        for(String s : tranList)
        {
            List<String> ENTER = toStringList(d.entered(s));
            List<String> EXIT = toStringList(d.exited(s));
            System.out.println("\nTransition:"+s);
            System.out.println("Entered:");
            for(String st : ENTER)System.out.print("|"+st);
            System.out.println("\nExited:");
            for(String st : EXIT)System.out.print("|"+st);

            String srcState = d.getTransSrc(s).toString();
            String destState = d.getTransDest(s).toString();
            ts.append("\n"+resolveName(s)+" == conf = "+resolveName(srcState)+" /\\ conf' = "+resolveName(destState));
        }

        ts.append("\n\nNext == ");
        for(String s : tranList)
        {
            ts.append("\n\t/\\ "+resolveName(s));
        }

        return ts.toString();
    }
    public static String Init(DashModule d)
    {
        StringBuilder init = new StringBuilder("\n\nInit == ");
        List<String> defaultsOfRoot = d.getDefaults(d.getRootName());
        for(String s : defaultsOfRoot)init.append("\n\t\\/ conf == "+resolveName(s));
        return init.toString();
    }
    public static List<String> toStringList(List<DashRef> dfs)
    {
        List<String> ls = new ArrayList<>();
        for(DashRef df : dfs)ls.add(df.toString());
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
