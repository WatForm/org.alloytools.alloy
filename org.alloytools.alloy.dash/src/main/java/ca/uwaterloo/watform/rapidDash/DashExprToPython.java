package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

import java.util.LinkedList;
import java.util.Deque;
import java.util.List;
import java.util.Map;


/*
    a class used to translate expressions to Python code
 */
public class DashExprToPython<ExprType> {
    private ExprType specialExpr;
    private Deque<StringBuilder> sbs;
    private Map<String, String> variable2StateNameMap;
    private String varName;;
    private List<DashPythonTranslation.Relation> relations;
    public boolean isDecl = false;
    public boolean isInit = false;

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap, String varName, List<DashPythonTranslation.Relation> relations){
        this.specialExpr = specialExpr;
        this.sbs = new LinkedList<>();
        this.sbs.addLast(new StringBuilder());
        this.variable2StateNameMap = variable2StateNameMap;
        this.varName = varName;
        this.relations = relations;

        // TODO: currently only support DashWhenExpr
        this.parseExpr();
    }

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap){
        this(specialExpr, variable2StateNameMap, "", null);
    }

    @Override
    public String toString() {
        return this.sbs.getLast().toString();
    }

    public List<String> toList(){
        List<String> result = new LinkedList<>();
        for (StringBuilder sb : sbs) {
            if (sb.length() > 0){
                result.add(sb.toString());
            }
        }
        return result;
    }
    
    public void reparseExpr() {
        sbs.removeLast();
        sbs.addLast(new StringBuilder());
    	parseExpr();
    }

    // generate python expressions
    private void parseExpr(){
        // TODO: need to handle predicates with multiple lines
        if(specialExpr instanceof DashWhenExpr){
            DashWhenExpr exp = (DashWhenExpr)this.specialExpr;
            sbs.getLast().append(genExpr(exp.getExpr(), exp.getAllExpressions().size()));
        } else if (specialExpr instanceof DashDoExpr){
            // TODO: Do expr should be different since actions are needed, not just evaluation statements
            DashDoExpr exp = (DashDoExpr)this.specialExpr;
            sbs.getLast().append(genExpr(exp.getExpr(), exp.getAllExpression().size()));
        } else {
            sbs.getLast().append(genExpr((Expr)specialExpr, 1));
        }
    }

    // print the expr tree using pre-order
    private String genExpr(Expr node, int size) {
        // TODO: currently, the second parameter is redundant

        // check type, there are two types of expr
        if (node instanceof  ExprList) {
            ExprList exprList = (ExprList) node;
            // Assuming each expr in the list is an independent statement
            for (Expr subNode : exprList.args) {
                sbs.getLast().append(genExpr(subNode, exprList.args.size()));
                sbs.addLast(new StringBuilder());
            }
            return "";
        }else if (node instanceof ExprUnary) {
            // TODO: is sub always a binary?

            ExprUnary unaryNode = (ExprUnary) node;
            return UnaryOp2PythonOp(unaryNode.op, unaryNode.sub);
        } else if (node instanceof ExprBinary) {
            // TODO: will BinaryExpr have sub nodes?

            // TODO: will need to replace left and right with signature names
            return BinaryOp2PythonOp((ExprBinary) node);
        } else if (node instanceof ExprVar || node instanceof ExprConstant){
            String varName = node.toString();
            if('\'' == node.toString().charAt(node.toString().length() - 1)){
                varName = node.toString().substring(0, node.toString().length() - 1);
            }
			return getVarName(varName);
        } else if (node instanceof ExprBadJoin) {
            // this assumes the expr is in the form (#STATE_VARIABLE).PLUS/MINUS[CONSTANT]
            ExprBadJoin badNode = (ExprBadJoin) node;
            ExprBadJoin badSubnode = (ExprBadJoin) badNode.right;
            ExprUnary cardinality = (ExprUnary) badSubnode.left;// #STATE_VARIABLE
            String type = badSubnode.right.toString();// plus or minus
            String operation = type.equals("plus") ? " + " : " - ";
            return UnaryOp2PythonOp(cardinality.op, cardinality.sub) + operation + badNode.left.toString();
        } else {
            // under development, use this to catch more types that could be useful
            System.out.println("[Warning] Need more types: " + node.getClass());
        }
        return "";
    }

    // translate Unary operation, also returns the empty space
    private String UnaryOp2PythonOp(ExprUnary.Op op, Expr node){
        String res = " ";
        switch (op){
            case LONEOF:    // State variable declaration
                res = node.toString() + "('" + varName + "', 0)";
                break;
            case ONEOF:     // State variable declaration
                res = node.toString() + "('" + varName + "', 1)";
                break;
            case SOMEOF:    // State variable declaration
                res = node.toString() + "('" + varName + "', 2)";
                break;
            case SETOF:     // State variable declaration
                res = node.toString() + "('" + varName + "', 3)";
                break;
            case EXACTLYOF:
                res = " ";
                break;
            case NOT:        // this part assumes the inner expression is a statement that evaluates to true or false
                res = "not(" + this.genExpr(node,1) + ")";
                break;
            case AFTER:
                res = " ";
                break;
            case ALWAYS:
                res = " ";
                break;
            case EVENTUALLY:
                res = " ";
                break;
            case BEFORE:
                res = " ";
                break;
            case HISTORICALLY:
                res = " ";
                break;
            case ONCE:
                res = " ";
                break;
            case NO:        // this part assumes the inner expression is a signature instance that is an object
                res = this.genExpr(node,1) + " is None";
                break;
            case SOME:      // this part assumes the inner expression is a signature instance that is an object
                res = this.genExpr(node,1) + " is not None";
                break;
            case LONE:
                res = " ";
                break;
            case ONE:
                res = " ";
                break;
            case TRANSPOSE:
                res = " ";
                break;
            case PRIME:
                res = " ";
                break;
            case RCLOSURE:
                res = " ";
                break;
            case CLOSURE:
                res = " ";
                break;
            case CARDINALITY:
                res = "len(self." + node.toString() + ")";
                break;
            case CAST2INT:
                res = " ";
                break;
            case CAST2SIGINT:
                res = " ";
                break;
            case NOOP:
                res = this.genExpr(node, 1);
                break;
        }
        return res;
    }

    // translate Binary operation, also returns the empty space
    private String BinaryOp2PythonOp(ExprBinary node){
        String res = " ";
        boolean addParanthesis = node.right instanceof ExprBinary;
        boolean rightConsumed = false;
        switch(node.op){
            case ARROW:     // State relation declaration
                // TODO: should apply this to other relation types.
            	// TODO: currently only support relation for exactly 2 types

                // Generate new relation name and add it to the list of relations.
                String newRelationName = node.left + "_" + node.right;
                String type = "[" + node.left + ", " + node.right  + "]";
                DashPythonTranslation.Relation newRelation = new DashPythonTranslation.Relation(newRelationName, type);
                if (relations != null && !relations.contains(newRelation)){ relations.add(newRelation); }
                res = newRelationName + "()";
                rightConsumed = true;
                break;
            case ANY_ARROW_SOME:
                res = " ";
                break;
            case ANY_ARROW_ONE:
                res = " ";
                break;
            case ANY_ARROW_LONE:
                res = " ";
                break;
            case SOME_ARROW_ANY:
                res = " ";
                break;
            case SOME_ARROW_SOME:
                res = " ";
                break;
            case SOME_ARROW_ONE:
                res = " ";
                break;
            case SOME_ARROW_LONE:
                res = " ";
                break;
            case ONE_ARROW_ANY:
                res = " ";
                break;
            case ONE_ARROW_SOME:
                res = " ";
                break;
            case ONE_ARROW_ONE:
                res = " ";
                break;
            case ONE_ARROW_LONE:
                res = " ";
                break;
            case LONE_ARROW_ANY:
                res = " ";
                break;
            case LONE_ARROW_SOME:
                res = " ";
                break;
            case LONE_ARROW_ONE:
                res = " ";
                break;
            case LONE_ARROW_LONE:
                res = " ";
                break;
            case ISSEQ_ARROW_LONE:
                res = " ";
                break;
            case JOIN:
                res = " ";
                break;
            case DOMAIN:
                res = " ";
                break;
            case RANGE:
                res = " ";
                break;
            case INTERSECT:
                res = " ";
                break;
            case PLUSPLUS:
                res = " ";
                break;
            case PLUS:        // this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + " + ";
                break;
            case IPLUS:
                res = " ";
                break;
            case MINUS:        // this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + " - ";
                break;
            case IMINUS:
                res = " ";
                break;
            case MUL:
                res = " ";
                break;
            case DIV:
                res = " ";
                break;
            case REM:
                res = " ";
                break;
            case EQUALS:        // this part assumes inner expression is a signature instances and are comparable
            	if(isInit) {
            		res = this.genExpr(node.left, 1) + " = " + this.genExpr(node.right, 1).toLowerCase();
            	} else {
            		res = this.genExpr(node.left, 1) + " = ";
            	}
                addParanthesis = false;
                break;
            case NOT_EQUALS:    // this part assumes inner expression is a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " != ";
                break;
            case IMPLIES:
                res = " ";
                break;
            case LT:         // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " < ";
                break;
            case LTE:        // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " <= ";
                break;
            case GT:         // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " > ";
                break;
            case GTE:        // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " >= ";
                break;
            case NOT_LT:     // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " >= ";
                break;
            case NOT_LTE:    // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " > ";
                break;
            case NOT_GT:     // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " <= ";
                break;
            case NOT_GTE:    // this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " < ";
                break;
            case SHL:
                res = " ";
                break;
            case SHA:
                res = " ";
                break;
            case SHR:
                res = " ";
                break;
            case IN:            // this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + " in ";
                break;
            case NOT_IN:        // this part assumes inner expression are a signature instances and are sets
                res = "not " + this.genExpr(node.left, 1) + " not in";
                break;
            case AND:           // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") and ";
                break;
            case OR:            // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") or ";
                break;
            case IFF:
                res = " ";
                break;
            case UNTIL:
                res = " ";
                break;
            case RELEASES:
                res = " ";
                break;
            case SINCE:
                res = " ";
                break;
            case TRIGGERED:
                res = " ";
                break;
        }

        // add paranthesis for right node
        if(addParanthesis){
            res += "(" + this.genExpr(node.right, 1) + ")";
        }else if (!rightConsumed){
            res += this.genExpr(node.right, 1);
        }
        return res;
    }

    private String getVarName(String varName){
        if (variable2StateNameMap.containsKey(varName)){
            return "SS." + variable2StateNameMap.get(varName) + "_" + varName;
        }
    	return varName;
    }
}
