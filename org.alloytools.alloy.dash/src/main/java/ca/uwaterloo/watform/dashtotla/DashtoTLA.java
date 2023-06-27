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
        return "\n\\*basic states"+basicStates;
    }
    public static String boilerplateCompositeStates(DashModule d)
    {
        List<String> states = d.getAllStateNames();
        StringBuilder compositeStates = new StringBuilder("");
        for(int i =0; i<states.size();i++)
        {
            String s = states.get(i);
            if(d.isLeaf(s))continue;
        }
        return "\n\\*composite states"+compositeStates;
    }
    public static String transitions(DashModule d)
    {
        // assumption - trigger and guard are tautologies
        StringBuilder ts = new StringBuilder("\n\n\\*transitions");
        List<String> tranList = d.getAllTransNames();
        for(String s : tranList)
        {
            String srcState = d.getTransSrc(s).toString();
            String destState = d.getTransDest(s).toString();
            ts.append("\n"+resolveName(s)+" == conf = "+srcState+" /\\ conf' = "+destState);
        }

        ts.append("\n\nNext == ");
        for(String s : tranList)
        {
            ts.append("/\\ "+resolveName(s)+"\n");
        }

        return ts.toString();
    }
}
