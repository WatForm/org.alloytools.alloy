package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

public class DashTransTemplate extends DashSuperAST {
    private List<Decl>    decls;

    private DashFrom      fromExpr;
    private DashOn        onExpr;
    private DashWhenExpr  whenExpr;
    private DashDoExpr    doExpr;
    private DashGoto      gotoExpr;
    public DashSend      sendExpr;

    public DashConcState parent   = null;

    public DashTransTemplate(Pos pos, String name, List<Object> stateItems, List<Decl> decls) {
        super(pos, name);
        this.setParameters(decls);

        for (Object item : stateItems) {
            if (item instanceof DashFrom)
                setOrigin((DashFrom) item);
            if (item instanceof DashOn)
                setTriggerEvent((DashOn) item);
            if (item instanceof DashDoExpr)
                setAction((DashDoExpr) item);
            if (item instanceof DashWhenExpr)
                setCondition((DashWhenExpr) item);
            if (item instanceof DashGoto)
                setDestination((DashGoto) item);
            if (item instanceof DashSend)
                sendExpr = (DashSend) item;
        }
    }

	public List<Decl> getParameters() {
		return decls;
	}

	public void setParameters(List<Decl> decls) {
		this.decls = decls;
	}

	public DashFrom getOrigin() {
		return fromExpr;
	}

	public void setOrigin(DashFrom fromExpr) {
		this.fromExpr = fromExpr;
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

	public DashGoto getDestination() {
		return gotoExpr;
	}

	public void setDestination(DashGoto gotoExpr) {
		this.gotoExpr = gotoExpr;
	}
}
