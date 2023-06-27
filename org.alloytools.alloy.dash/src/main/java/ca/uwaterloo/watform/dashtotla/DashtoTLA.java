package ca.uwaterloo.watform.dashtotla;


import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.parser.*;

public class DashtoTLA 
{
    public static String translate(DashModule d)
    {
        if(!d.hasRoot())
        {
            System.out.println("Error - no root state, nothing to translate");
            return "";
        }
        StringBuilder things = new StringBuilder();

        List<String> states = d.getAllStateNames();
        StringBuilder constants = new StringBuilder("");
        for(int i =0; i<states.size();i++)
            {
                String s = states.get(i);
                if(d.isLeaf(s))constants.append("\n"+resolveName(s)+"=="+i);
            }


        return "\n\\*basic states"+constants;
    }
    public static String resolveName(String s)
    {
        return s.replace("/", "_");
    }
}
