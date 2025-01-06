package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashInv extends DashExpr {

    String name; // unused

    public DashInv(Pos p, Expr inv) {
        super(p,inv);
 
    }

    public DashInv(Pos p, String n, Expr inv) {
        super(p,inv);
        this.name = n;
    }

    // copy cons for deep copy
    public DashInv(DashInv other) {
        super(other.pos, other.exp);
        if(other.name == null) {
            this.name = new String();
        }
        else {
            this.name = new String(other.name);
        }
    }

    public String toString() {
        return super.toString(DashStrings.invName + " "+name);
    }
}