package ca.uwaterloo.watform.dashtotla;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.parser.DashModule;

public class Transition 
{
    public static final String EXISTS_ENABLED_TRANSITION = "_exists_enabled_tranistions";

    public static String postCondition(DashModule d, String trans)
    {
        StringBuilder code = new StringBuilder("");

        // conf'
        List<String> entered = Util.toStringList(d.entered(trans));
        List<String> exited = Util.toStringList(d.exited(trans));
        String confPrimed = "\n\t"+TLA.AND+" "+Variable.prime(Variable.CONF)+TLA.EQUAL
                                +TLA.parenthesis(Variable.CONF+" "+TLA.SET_DIFFERENCE+" "+TLA.set(Util.resolveList(exited)))+" "+TLA.UNION+" "
                                +TLA.set(Util.resolveList(entered));
        
        // scopes_used'
        List<String> scopesUsed = Util.toStringList(d.scopesUsed(trans));
        String scopes = "\n\t"+TLA.AND+" "+Variable.prime(Variable.SCOPES_USED)+TLA.EQUAL+Variable.SCOPES_USED+" "+TLA.UNION+" "+TLA.set(Util.resolveList(scopesUsed));

        code.append(confPrimed);
        code.append(scopes);
        code.append("\n\t"+TLA.AND+" "+Variable.prime(Variable.ENVIRONMENTAL_EVENTS)+TLA.EQUAL+Variable.ENVIRONMENTAL_EVENTS);
        return code.toString();
    }
    public static String preCondition(DashModule d, String trans)
    {
        StringBuilder code = new StringBuilder("");

        // conf
        String srcState = d.getTransSrc(trans).toString();
        String conf = "\n\t"+TLA.AND+" "+State.isInState(srcState);

        // formula for events
        DashRef on = d.getTransOn(trans);
        String events = "";
        if(on!=null)events = "\n\t"+TLA.AND+" "+TLA.set(Util.resolveName(on.getName()))+" "+TLA.SUBSET+" "+Variable.INTERNAL_EVENTS;

        // scopes_used
        List<String> nonOrthogonalScopes = Util.toStringList(d.nonOrthogonalScopesOf(trans));
        String scopes = "\n\t"+TLA.AND+" "+Variable.SCOPES_USED+" "+TLA.INTERSECTION+" "+TLA.set(Util.resolveList(nonOrthogonalScopes))+TLA.EQUAL+TLA.NULL_SET;

        code.append(conf);
        code.append(events);
        code.append(scopes);
        return code.toString();
    }
    public static String transitions(DashModule d)
    {
        // assumption - guard is tautology
        StringBuilder ts = new StringBuilder("\n\n"+TLA.comment("transitions"));
        List<String> tranList = d.getAllTransNames();
        List<String> preCondList = new ArrayList<>();
        for(String s : tranList)
        {
            String preConditionName = "_pre__"+Util.resolveName(s);
            String postConditionName = "_post__"+Util.resolveName(s);
            ts.append("\n\n"+preConditionName+" "+TLA.DEFINE+" "+preCondition(d, s));
            ts.append("\n"+postConditionName+" "+TLA.DEFINE+" "+postCondition(d, s));
            ts.append("\n"+Util.resolveName(s)+" "+TLA.DEFINE+" "+preConditionName+" "+TLA.AND+" "+postConditionName);
            preCondList.add(preConditionName);
        }

        StringBuilder somePrecond = new StringBuilder("\n\n"+EXISTS_ENABLED_TRANSITION+" "+TLA.DEFINE+" ");
        for(String s : preCondList)
            somePrecond.append("\n\t"+TLA.AND+" "+s);

        return ts.append(somePrecond).toString();
    }
}
