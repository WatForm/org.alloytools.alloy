package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.*;

import java.util.*;


/*
    a class used to translate expressions to Python code
 */
public class DashExprToPython<ExprType> {
    enum ExprTypeE {
        DO, PRED, DEFAULT
    }
    private final String varTrackerName = "SS.";
    private ExprTypeE exprType;
    private ExprType specialExpr;
    private Deque<StringBuilder> sbs;
    private Map<String, String> variable2StateNameMap;
    private String varName;;
    private List<DashPythonTranslation.Relation> relations;
    public boolean isDecl = false;
    public boolean isInit = false;
    // used to store the dynamic variables that are related to the current expression
    // only used for invariants
    private Set<String> relatedDynamicVars;
    private List<String> assignableVars;

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap, String varName, List<DashPythonTranslation.Relation> relations, ExprTypeE exprType){
        this.specialExpr = specialExpr;
        this.sbs = new LinkedList<>();
        this.sbs.addLast(new StringBuilder());
        this.variable2StateNameMap = variable2StateNameMap;
        this.varName = varName;
        this.relations = relations;
        this.exprType = exprType;
        this.relatedDynamicVars = new HashSet<>();
        this.assignableVars = new LinkedList<>();

        // TODO: currently only support DashWhenExpr
        this.parseExpr();
    }

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap, String varName, List<DashPythonTranslation.Relation> relations){
        this(specialExpr, variable2StateNameMap, varName, relations, ExprTypeE.DEFAULT);
    }

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap, ExprTypeE exprType){
        this(specialExpr, variable2StateNameMap, "", null, exprType);
    }

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap){
        this(specialExpr, variable2StateNameMap, "", null, ExprTypeE.DEFAULT);
    }

    @Override
    public String toString() {
        return this.sbs.getLast().toString().trim();
    }

    public List<String> toList(){
        List<String> result = new LinkedList<>();
        for (StringBuilder expr : sbs){
            String trimmedExpr = expr.toString().trim();
            if (trimmedExpr.length() == 0 || trimmedExpr.equals("\n")){
                continue;
            }
            // Concatenate to the previous expression.
            if(ExprTypeE.PRED == exprType){
                // Format the predicate.
                if (expr.charAt(0) == ')') {
                    result.set(result.size() - 1, result.get(result.size() - 1).concat(trimmedExpr));
                }else if(trimmedExpr.equals("or") || trimmedExpr.equals("and")){
                    result.set(result.size() - 1, result.get(result.size() - 1).concat(" " + trimmedExpr));
                }else{
                    result.add(trimmedExpr);
                }
            }else{
                result.add(trimmedExpr);
            }
        }
        return result;
    }

    public Set<String> getRelatedDynamicVars() {return relatedDynamicVars;}
    public List<String> getAssignableVars() {return assignableVars;}

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
            Iterator<Expr> subNode = exprList.args.iterator();

            if (1 == exprList.args.size()){
                sbs.getLast().append(genExpr(subNode.next(), exprList.args.size()));
                sbs.addLast(new StringBuilder());
                return "";
            }

            // predicates need to be wrapped in () and must be linked with and/or operators
            if (ExprTypeE.PRED == exprType) {
                sbs.getLast().append("(");
                while (subNode.hasNext()) {
                    sbs.getLast().append(genExpr(subNode.next(), exprList.args.size()));
                    // linkOperators
                    if (subNode.hasNext()) {
                        if (exprList.op == ExprList.Op.AND) {
                            sbs.getLast().append(" and ");
                        } else if (exprList.op == ExprList.Op.OR) {
                            sbs.getLast().append(" or ");
                        }
                    } else {
                        sbs.getLast().append(")");
                    }
                    sbs.addLast(new StringBuilder());
                }
            } else {
                while (subNode.hasNext()) {
                    sbs.getLast().append(genExpr(subNode.next(), exprList.args.size()));
                    sbs.addLast(new StringBuilder());
                }
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
            if('\'' == varName.charAt(varName.length() - 1)){   // primed variable
                varName = varName.substring(0, varName.length() - 1);
                assignableVars.add(varName);
            }
			return getVarName(varName);
        } else if (node instanceof ExprBadJoin) {
            // this assumes the expr is in the form (#STATE_VARIABLE).PLUS/MINUS[CONSTANT]
            ExprBadJoin badNode = (ExprBadJoin) node;
            if (badNode.right instanceof ExprBadJoin){
                ExprBadJoin badSubnode = (ExprBadJoin) badNode.right;
                ExprUnary cardinality = (ExprUnary) badSubnode.left;// #STATE_VARIABLE
                String type = badSubnode.right.toString();// plus or minus
                String operation = type.equals("plus") ? " + " : " - ";
                return UnaryOp2PythonOp(cardinality.op, cardinality.sub) + operation + badNode.left.toString();
            } else if (badNode.right instanceof ExprVar){
                // This probably means it's a map (e.g., A.B => A[B])
                // TODO: this is a hack and did not handle the case, only to prevent exceptions, need to fix
                String nodeLeft = genExpr(badNode.left, 1);
                String nodeRight = genExpr(badNode.right, 1);
                return nodeLeft + "." + nodeRight;
            } else {
                System.out.println("[Warning] BadNode needs more types: " + node.getClass());
            }
        } else if (node instanceof ExprQt) {
            // Expression with quantifiers
            ExprQt qtNode = (ExprQt) node;
            StringBuilder quantifiedSource = new StringBuilder();

            // format: quantifier variable:type | formula

            for(Decl decl : qtNode.decls){
                // Get type/declaration of the quantified variables
                String quantifiedDecl = genExpr(decl.expr, 1);

                // Get the quantified variables
                for (ExprHasName variable : decl.names) {
                    if (quantifiedSource.length() > 0){
                        quantifiedSource.append(" ");
                    }
                    quantifiedSource.append(String.format("for %s in %s", genExpr(variable, 1), quantifiedDecl));
                }
            }
            // Get the formula of the quantified expression
            Deque<StringBuilder> sbsTemp = sbs;
            this.sbs = new LinkedList<>();
            this.sbs.addLast(new StringBuilder());
            String quantifiedFormula = genExpr(qtNode.sub, 1);
            // Meaning there are several statements in the quantified formula
            if(!sbs.getFirst().toString().isEmpty()){
                quantifiedFormula = String.join(" ", toList());
            }
            sbs = sbsTemp;

            // TODO: SUM and COMPREHENSION needs further implementation, currently only support them with one variable
            // Get the quantifier for list comprehension
            switch (qtNode.op) {
                case ALL:   // All true
                    return String.format("all([%s %s])", quantifiedFormula, quantifiedSource);
                case NO:    // No true
                    return String.format("not any([%s %s])", quantifiedFormula, quantifiedSource);
                case LONE:  // one or no true
                    return String.format("(1 >= [%s %s].count(True))", quantifiedFormula, quantifiedSource);
                case ONE:   // exactly one true
                    return String.format("(1 == [%s %s].count(True))", quantifiedFormula, quantifiedSource);
                case SOME:  // at least one true
                    return String.format("any([%s %s])", quantifiedFormula, quantifiedSource);
                case SUM:   // sum of values
                    return String.format("sum([%s %s if %s])", qtNode.decls.get(0).names.get(0).toString(), quantifiedSource, quantifiedFormula);
                case COMPREHENSION: // list comprehension
                    return String.format("[%s %s if %s]", qtNode.decls.get(0).names.get(0).toString(), quantifiedSource, quantifiedFormula);
            }
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
                res = "not any(" + this.genExpr(node,1) + ")";
                break;
            case SOME:      // this part assumes the inner expression is a signature instance that is an object
                res = "any(" + this.genExpr(node,1) + ")";
                break;
            case LONE:
                res = "(1 >= len(" + this.genExpr(node,1) + "))";
                break;
            case ONE:
                res = "(1 == len(" + this.genExpr(node,1) + "))";
                break;
            case TRANSPOSE:
                res = " ";
                break;
            case PRIME:
                // TODO: don't think we need this
                res = " ";
                break;
            case RCLOSURE:
                res = " ";
                break;
            case CLOSURE:
                res = " ";
                break;
            case CARDINALITY:
                res = "len(" + this.genExpr(node,1) + ")";
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
        boolean shouldDddParenthesis = node.right instanceof ExprBinary;
        boolean rightConsumed = false;  // if the right expression is already parsed
        switch(node.op){
            case ARROW:     // State relation declaration
                // TODO: should apply this to other relation types.
            	// TODO: currently only support relation for exactly 2 types

                // Generate new relation name and add it to the list of relations.
                res = getVarName(node.left.toString()) + " * " + getVarName(node.right.toString());

                // TODO: we assume the model can always be solved by Alloy Solver
                /* [Deprecated]: now the Alloy Solver will handle the initialization of relations
                    String type = "[" + node.left + ", " + node.right  + "]";
                    DashPythonTranslation.Relation newRelation = new DashPythonTranslation.Relation(newRelationName, type);
                    if (relations != null && !relations.contains(newRelation)){ relations.add(newRelation); }
                    res = newRelationName + "()";
                 */

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
            	if(isInit) {    // TODO: this should be deprecated if we assume the Alloy Solver can always handle the initialization
            		res = this.genExpr(node.left, 1) + " = " + this.genExpr(node.right, 1).toLowerCase();
            	} else if (ExprTypeE.DO == exprType){
                    // TODO: delete this part if we assume the Alloy Solver can always handle the initialization
            		res = varTrackerName + this.genExpr(node.left, 1).substring(varTrackerName.length()) + " = ";
            	} else {        // predicates
                    res = this.genExpr(node.left, 1) + " == ";
                }
                shouldDddParenthesis = false;
                break;
            case NOT_EQUALS:    // this part assumes inner expression is a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " != ";
                break;
            case IMPLIES:
                res = " ";
                break;
            case LT:         // this part assumes inner expression are a signature instances and are comparable
            case NOT_GTE:
                res = this.genExpr(node.left, 1) + " < ";
                break;
            case LTE:        // this part assumes inner expression are a signature instances and are comparable
            case NOT_GT:
                res = this.genExpr(node.left, 1) + " <= ";
                break;
            case GT:         // this part assumes inner expression are a signature instances and are comparable
            case NOT_LTE:
                res = this.genExpr(node.left, 1) + " > ";
                break;
            case GTE:        // this part assumes inner expression are a signature instances and are comparable
            case NOT_LT:
                res = this.genExpr(node.left, 1) + " >= ";
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
                res = this.genExpr(node.left, 1) + " not in ";
                break;
            case AND:           // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") and ";
                break;
            case OR:            // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") or ";
                break;
            case IFF:
                res = "(" + this.genExpr(node.left, 1) + ") == ";
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

        // add the right expression node
        if (!rightConsumed){
            if(shouldDddParenthesis) {
                res += "(" + this.genExpr(node.right, 1) + ")";
            }else{
                res += this.genExpr(node.right, 1);
            }
        }
        return res;
    }

    private String getVarName(String varName){
        if (varName.contains("/")){
            String[] parts = varName.split("/");
            relatedDynamicVars.add(parts[parts.length - 1]);
            return varTrackerName + varName.replace("/", "_");
        }
        if (variable2StateNameMap.containsKey(varName)){
            relatedDynamicVars.add(varName);
            return varTrackerName + variable2StateNameMap.get(varName) + "_" + varName;
        }
    	return varName;
    }
}
