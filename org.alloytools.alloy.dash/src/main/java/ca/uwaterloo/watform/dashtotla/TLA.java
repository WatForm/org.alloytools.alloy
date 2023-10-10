package ca.uwaterloo.watform.dashtotla;

import java.util.List;

public class TLA
{
    public static final String EQUAL = "=";
    public static final String DEFINE = "==";

    public static final String AND = "/\\";
    public static final String OR = "\\/";
    public static final String NOT = "~";

    public static final String FOR_ALL = "\\A";
    public static final String EXISTS = "\\E";
    public static final String IN = "\\in";
    public static final String PREDICATE_SCOPE = "\\:";

    public static final String TRUE = "TRUE";
    public static final String FALSE = "FALSE";

    public static final String[] MODULES = new String[]{"Integers","FiniteSets"};

    public static final String UNION = "\\union";
    public static final String INTERSECTION = "\\intersect";
    public static final String NULL_SET = set("");
    public static final String SUBSET = "\\subseteq";
    public static final String PROPER_SUBSET = "\\subset";
    public static final String SUPERSET = "\\superseteq";
    public static final String PROPER_SUPERSET = "\\superset";
    public static final String SET_DIFFERENCE = "\\";

    public static String parenthesis(String exp){return "("+exp+")";}
    public static String comment(String comment){return "\\* "+comment;}
    public static String commentMultiLine(String comment){return "\n(*"+comment+"\n*)";}
    public static String set(String exp){return "{"+exp+"}";}
    public static String string(String exp){return "\""+exp+"\"";}
    public static String cardinality(String exp){return "Cardinality("+exp+")";}
    public static String set(List<String> elements) // set in TLA+ notation
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
    public static String header(String moduleName)
    {
        return "------------------------------- MODULE "+moduleName+" -------------------------------";
    }
    public final static String FOOTER = "=============================================================================";
    public static String extend(String externalModules[])
    {
        if(externalModules.length==0)return "";
        StringBuilder code = new StringBuilder("EXTENDS ");
        for(int i=0;i<externalModules.length-1;i++)
            code.append(externalModules[i]+", ");
        code.append(externalModules[externalModules.length-1]);
        return code.toString();
    }
    public static String variables(List<String> variables)
    {
        if(variables.size()==0)return "";
        StringBuilder code = new StringBuilder("VARIABLES ");
        for(int i=0;i<variables.size()-1;i++)
            code.append(variables.get(i)+", ");
        code.append(variables.get(variables.size()-1));
        return code.toString();
    }
}