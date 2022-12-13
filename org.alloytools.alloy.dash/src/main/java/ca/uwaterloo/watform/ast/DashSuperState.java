package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

/*
 * The Base Class for DashState and DashConcState sub-class
 */
public abstract class DashSuperState extends DashSuperAST {
	protected List<DashConcState>      	concStates;
    protected List<DashState>          	states;
    protected List<DashTrans> 		  	transitions;
    protected List<Decl>          		decls;
    protected List<DashEvent>    		events;
    protected List<DashBuffer>    		buffers;
    protected List<DashInvariant>     	invariant;
    
    public DashSuperState(Pos pos, String name) {
		super(pos, name);
		this.initializeContainers();
	}
    
    private void initializeContainers() {
    	concStates     = new ArrayList<DashConcState>();
        states         = new ArrayList<DashState>();
        transitions    = new ArrayList<DashTrans>();
        decls          = new ArrayList<Decl>();
        events         = new ArrayList<DashEvent>();
        buffers        = new ArrayList<DashBuffer>();
        invariant      = new ArrayList<DashInvariant>();
    }
    
    public abstract List<DashConcState>  getInnerConcStates();
    public abstract List<DashState>		 getInnerORStates();
    public abstract List<DashTrans> 	 getTransitions();
	public abstract List<DashBuffer>	 getBuffers();
	public abstract List<DashEvent>		 getEvents();
	public abstract List<Decl> 			 getVariables();
}
