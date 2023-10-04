package ca.uwaterloo.watform.dashtotla;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashOptions;

public class DashToTLA 
{

    public static String translate(Object[] args) throws Exception
    {
        if(args.length!=2)throw new Exception("Invalid arguments to translate to TLA");
        
        DashModule d = (DashModule)args[0];
        String moduleName = (String)args[1];
        boolean singleEnvInput = DashOptions.singleEventInput;

        if(!d.hasRoot())throw new Exception("Error - no root state, nothing to translate");

        StringBuilder code = new StringBuilder("");
        code.append(TLA.header(moduleName));
        code.append("\n"+TLA.extend(TLA.MODULES));
        code.append(Variable.declareVariables(d));
        code.append(Atom.leafStates(d));
        code.append(Atom.nonLeafStates(d));
        code.append(Atom.internalEvents(d));
        code.append(Atom.environmentalEvents(d));
        code.append(Variable.supersets(d));
        code.append(Variable.initialValues(d));
        code.append(StandardFormulae.TypeOK(d));
        code.append(State.createInStates(d));
        code.append(Transition.transitions(d));
        code.append(StandardFormulae.Init(d,singleEnvInput));
        code.append(StandardFormulae.Stutter(d,singleEnvInput));
        code.append(StandardFormulae.Next(d));
        code.append("\n"+TLA.FOOTER);
        code.append("\n"+TLA.comment("Modification History")+
                    "\n"+TLA.comment("Translated from Dash at "+System.currentTimeMillis()+" EPOCH"));
        
        return code.toString();
    } 
}