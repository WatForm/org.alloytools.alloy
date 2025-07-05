package ca.uwaterloo.watform.predabstraction;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Command;

public class AbstractionQuery {

        public String commandName;
        public Command command;
        public String predName;
        public QueryType qtype;
        public Boolean result = null;
        public Boolean absPredNegated;
        public Expr absPred;
        public AbstractionQuery conjugate;
        public String predBody;
        public String cmdBody;

        public enum QueryType {
            INIT,
            INV,
            GUARD,
            ACTION,
            PROPERTY;

        }

        public AbstractionQuery(String cname, String pname, QueryType t, Expr pred, Boolean neg) {
            this.commandName = cname;
            this.predName = pname;
            this.qtype = t;
            this.absPredNegated = neg;
            this.absPred = pred;
        }

        public void setCommand(Command c) {
            this.command = c;
        }

        public void setResult(Boolean r) {
            this.result = r;
        }

        public void setPredBody(String body){
            this.predBody = body;
        }

        public void setCmdBody(String body){
            this.cmdBody = body;
        }

        public void setConjugateQuery(AbstractionQuery q) {
            assert(this.absPredNegated != q.absPredNegated && this.absPred == q.absPred);
            this.conjugate = q;
        }

        public boolean isInitQuery(){
            return (qtype == QueryType.INIT);
        }
        public boolean isInvQuery(){
            return (qtype == QueryType.INV);
        }
        public boolean isGuardQuery(){
            return (qtype == QueryType.GUARD);
        }
        public boolean isActionQuery(){
            return (qtype == QueryType.ACTION);
        }
        public boolean isPropertyQuery() {
            return (qtype == QueryType.PROPERTY);
        }
        public boolean isQueryNegatedPredicate() {
            return absPredNegated;
        }
    }