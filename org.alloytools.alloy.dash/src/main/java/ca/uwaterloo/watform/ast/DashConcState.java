package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

/* This class is responsible for holding information regarding each concurrent state
 * declared within a DASH model */
public class DashConcState {

    public Pos                     pos;
    public String                  name         = "";
    public String                  modifiedName = "";
    public DashConcState           parent;

    public List<DashConcState>     concStates   = new ArrayList<DashConcState>();
    public List<DashState>         states       = new ArrayList<DashState>();
    public List<DashTrans>         transitions  = new ArrayList<DashTrans>();
    public List<DashTemplateCall>  templateCall = new ArrayList<DashTemplateCall>();
    public List<DashTransTemplate> templateDecl = new ArrayList<DashTransTemplate>();
    public List<DashEvent>         events       = new ArrayList<DashEvent>();
    public List<Decl>              decls        = new ArrayList<Decl>();
    public List<DashInit>          init         = new ArrayList<DashInit>();
    public List<DashInvariant>     invariant    = new ArrayList<DashInvariant>();
    public List<DashAction>        action       = new ArrayList<DashAction>();
    public List<DashCondition>     condition    = new ArrayList<DashCondition>();

    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * concurrent state. concStateItems are the list of items that are inside the
     * parsed conc state.
     */
    public DashConcState(Pos pos, String name, List<Object> concStateItems) {
        this.pos = pos;
        this.name = name;

        //Iterate through each item in the conc state and add each item to
        //a respective list (A state item will be added to the list of states, etc)
        for (Object item : concStateItems) {
            if (item instanceof DashConcState)
                concStates.add((DashConcState) item);
            if (item instanceof DashState)
                states.add((DashState) item);
            if (item instanceof DashTrans)
                transitions.add((DashTrans) item);
            if (item instanceof Decl)
                decls.add((Decl) item);
            if (item instanceof DashEvent)
                events.add((DashEvent) item);
            if (item instanceof DashInit)
                init.add((DashInit) item);
            if (item instanceof DashInvariant)
                invariant.add((DashInvariant) item);
            if (item instanceof DashAction)
                action.add((DashAction) item);
            if (item instanceof DashCondition)
                condition.add((DashCondition) item);
            if (item instanceof DashTemplateCall)
                templateCall.add((DashTemplateCall) item);
            if (item instanceof DashTransTemplate)
                templateDecl.add((DashTransTemplate) item);
        }
    }
}
