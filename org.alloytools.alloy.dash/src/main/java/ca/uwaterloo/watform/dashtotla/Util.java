package ca.uwaterloo.watform.dashtotla;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.parser.DashModule;

public class Util 
{
    public static String resolveName(String s) // get rid of unsupported characters in full names
    {
        char SP = '_';  // SP is a specual character that cannot appear in any variablename in dash, but can in TLA+
        return SP+s.replace('/', SP);
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
    
    public static List<String> resolveList(List<String> elements) // set of strings in TLA+ notation
    {
        List<String> resolvedNames = new ArrayList<>();
        elements.forEach(element -> {resolvedNames.add(resolveName(element));});
        return resolvedNames;
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
