package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

/* Stores information regarding a transition within a state/concState */
public class DashTrans extends DashSuperAST {
    private DashFrom          fromExpr;
    private DashOn            onExpr;
    private DashWhenExpr      whenExpr;
    private DashDoExpr        doExpr;
    private DashGoto          gotoExpr;
    private DashSend          sendExpr;
    private DashTransTemplate transTemplate;

    /*
     * TransItems is the list of items that is inside a transition. An example of an
     * items is do statement, goto statement, etc.
     */
    public DashTrans(Pos pos, String name, List<Object> transItems) {
    	super(pos, name);

        for (Object item : transItems) {
            if (item instanceof DashFrom)
                fromExpr = (DashFrom) item;
            if (item instanceof DashOn)
                setTriggerEvent((DashOn) item);
            if (item instanceof DashWhenExpr)
                setCondition((DashWhenExpr) item);
            if (item instanceof DashDoExpr)
                setAction((DashDoExpr) item);
            if (item instanceof DashGoto)
                setDestination((DashGoto) item);
            if (item instanceof DashSend)
                setEventsTriggered((DashSend) item);

        }
    }

    public DashTrans(DashTrans trans) {
    	super(trans.pos, trans.name);
        this.setOrigin(trans.fromExpr);
        this.setTriggerEvent(trans.getTriggerEvent());
        this.setCondition(trans.getCondition());
        this.setAction(trans.getAction());
        this.setDestination(trans.getDestination());
        this.setEventsTriggered(trans.getEventsTriggered());

        this.modifiedName = trans.modifiedName;
        this.parent = trans.parent;
        this.parentConcState = trans.parentConcState;
    }
    
    public DashFrom getOrigin() {
    	return this.fromExpr;
    }
    
    public void setOrigin(DashFrom fromExpr) {
    	this.fromExpr = fromExpr;
    }
    
    public DashGoto getDestination() {
    	return this.gotoExpr;
    }
    
    public DashDoExpr getActions() {
    	return getAction();
    }
    
    public DashSend getEventTriggered() {
    	return getEventsTriggered();
    }
    
    public DashOn getTriggerEvent() {
    	return onExpr;
    }

	public void setTriggerEvent(DashOn onExpr) {
		this.onExpr = onExpr;
	}

	public DashWhenExpr getCondition() {
		return whenExpr;
	}

	public void setCondition(DashWhenExpr whenExpr) {
		this.whenExpr = whenExpr;
	}

	public DashDoExpr getAction() {
		return doExpr;
	}

	public void setAction(DashDoExpr doExpr) {
		this.doExpr = doExpr;
	}

	public void setDestination(DashGoto gotoExpr) {
		this.gotoExpr = gotoExpr;
	}

	public DashSend getEventsTriggered() {
		return sendExpr;
	}

	public void setEventsTriggered(DashSend sendExpr) {
		this.sendExpr = sendExpr;
	}

	public DashTransTemplate getTransTemplate() {
		return transTemplate;
	}

	public void setTransTemplate(DashTransTemplate transTemplate) {
		this.transTemplate = transTemplate;
	}
	
	public boolean hasOriginState() {
		return this.getOrigin().getAllOrigins().size() > 0;
	}
	
	public boolean hasDestinationState() {
		return this.getDestination().getAllDestinations().size() > 0;
	}
}
