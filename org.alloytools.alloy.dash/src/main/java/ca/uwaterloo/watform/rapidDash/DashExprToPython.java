package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.*;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/*
    a class used to translate expressions to Python code
 */
public class DashExprToPython<ExprType> {
    enum ExprTypeE {
        INV, DO, DEFAULT
    }
    public static final String VarTrackerName = "SS.";
    public static final String VarLocalSuffix = "_updated";
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

    private final VariableSet relatedDynamicVars;      // All related variables, including the ones that are not assignable
    private final VariableSet assignableVars;          // All assignable variables

    public DashExprToPython(ExprType specialExpr, Map<String, String> variable2StateNameMap, String varName, List<DashPythonTranslation.Relation> relations, ExprTypeE exprType){
        this.specialExpr = specialExpr;
        this.sbs = new LinkedList<>();
        this.sbs.addLast(new StringBuilder());
        this.variable2StateNameMap = variable2StateNameMap;
        this.varName = varName;
        this.relations = relations;
        this.exprType = exprType;
        this.relatedDynamicVars = new VariableSet();
        this.assignableVars = new VariableSet();

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
            if (expr.charAt(0) == ')') {
                result.set(result.size() - 1, result.get(result.size() - 1).concat(trimmedExpr));
            }else if(trimmedExpr.equals("or") || trimmedExpr.equals("and")){
                result.set(result.size() - 1, result.get(result.size() - 1).concat(" " + trimmedExpr));
            }else{
                result.add(trimmedExpr);
            }
        }
        return result;
    }

    public VariableSet getRelatedDynamicVars() {return relatedDynamicVars;}
    public VariableSet getAssignableVars() {return assignableVars;}

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
            sbs.getLast().append(genExpr(exp.getExpr()));
        } else if (specialExpr instanceof DashDoExpr){
            DashDoExpr exp = (DashDoExpr)this.specialExpr;
            sbs.getLast().append(genExpr(exp.getExpr()));
        } else {
            sbs.getLast().append(genExpr((Expr)specialExpr));
        }
    }

    // print the expr tree using pre-order
    private String genExpr(Expr node) {
        // TODO: currently, the second parameter is redundant

        // check type, there are two types of expr
        if (node instanceof  ExprList) {
            ExprList exprList = (ExprList) node;
            // Assuming each expr in the list is an independent statement
            Iterator<Expr> subNode = exprList.args.iterator();

            if (1 == exprList.args.size()){
                sbs.getLast().append(genExpr(subNode.next()));
                sbs.addLast(new StringBuilder());
                return "";
            }

            // predicates need to be wrapped in () and must be linked with and/or operators
            sbs.getLast().append("(");
            while (subNode.hasNext()) {
                sbs.getLast().append(genExpr(subNode.next()));
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

            return "";
        }else if (node instanceof ExprUnary) {
            // TODO: is sub always a binary?

            ExprUnary unaryNode = (ExprUnary) node;
            return UnaryOp2PythonOp(unaryNode.op, unaryNode.sub);
        } else if (node instanceof ExprBinary) {
            return BinaryOp2PythonOp((ExprBinary) node);
        } else if (node instanceof ExprVar || node instanceof ExprConstant){
            String varName = node.toString();
            Variable var;
            switch(exprType){
                case INV:   // Invariant variables will be parameterized, so no change to the names
                    var = getVarName(varName);
                    return var.getName();
                case DO:    // Prime variables will have a suffix in the actions
                    if('\'' == varName.charAt(varName.length() - 1)){
                        var = getVarName(varName.substring(0, varName.length() - 1));
                        var.setHasSuffix(true);
                        assignableVars.add(var);
                        return var.getLocalName();
                    }
                    break;
                default:
                    break;
            }
			return getVarName(varName).getQualName();
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
                // Join operation (e.g., A.B => A ^ B)
                return "(" + genExpr(badNode.left) + " ^ " + genExpr(badNode.right) + ")";
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
                String quantifiedDecl = genExpr(decl.expr);

                // Get the quantified variables
                for (ExprHasName variable : decl.names) {
                    if (quantifiedSource.length() > 0){
                        quantifiedSource.append(" ");
                    }
                    quantifiedSource.append(String.format("for %s in %s", genExpr(variable), quantifiedDecl));
                }
            }
            // Get the formula of the quantified expression
            Deque<StringBuilder> sbsTemp = sbs;
            this.sbs = new LinkedList<>();
            this.sbs.addLast(new StringBuilder());
            String quantifiedFormula = genExpr(qtNode.sub);
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
                res = node.toString() + "('" + varName + "', Multiplicity.Lone)";
                break;
            case ONEOF:     // State variable declaration
                res = node.toString() + "('" + varName + "', Multiplicity.One)";
                break;
            case SOMEOF:    // State variable declaration
                res = node.toString() + "('" + varName + "', Multiplicity.Some)";
                break;
            case SETOF:     // State variable declaration
                res = node.toString() + "('" + varName + "', Multiplicity.Set)";
                break;
            case EXACTLYOF:
                res = " ";
                break;
            case NOT:        // this part assumes the inner expression is a statement that evaluates to true or false
                res = "not(" + this.genExpr(node) + ")";
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
                res = "not any(" + this.genExpr(node) + ")";
                break;
            case SOME:      // this part assumes the inner expression is a signature instance that is an object
                res = "any(" + this.genExpr(node) + ")";
                break;
            case LONE:
                res = "(1 >= len(" + this.genExpr(node) + "))";
                break;
            case ONE:
                res = "(1 == len(" + this.genExpr(node) + "))";
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
                res = "len(" + this.genExpr(node) + ")";
                break;
            case CAST2INT:
                res = " ";
                break;
            case CAST2SIGINT:
                res = " ";
                break;
            case NOOP:
                res = this.genExpr(node);
                break;
        }
        return res;
    }

    // translate Binary operation, also returns the empty space
    private String BinaryOp2PythonOp(ExprBinary node){
        String res = " ";
        boolean shouldAddParenthesis = node.right instanceof ExprBinary;
        boolean rightConsumed = false;  // if the right expression is already parsed
        switch(node.op){
            case ARROW: // Cartesian product
                res = this.genExpr(node.left) + " * ";
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
                res = this.genExpr(node.left) + " ^ ";
                shouldAddParenthesis = true;
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
                res = this.genExpr(node.left) + " + ";
                break;
            case IPLUS:
                res = " ";
                break;
            case MINUS:        // this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left) + " - ";
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
            		res = this.genExpr(node.left) + " = " + this.genExpr(node.right).toLowerCase();
            	} else {        // predicates
                    res = this.genExpr(node.left) + " == ";
                }
                shouldAddParenthesis = false;
                break;
            case NOT_EQUALS:    // this part assumes inner expression is a signature instances and are comparable
                res = this.genExpr(node.left) + " != ";
                break;
            case IMPLIES:
                res = " ";
                break;
            case LT:         // this part assumes inner expression are a signature instances and are comparable
            case NOT_GTE:
                res = this.genExpr(node.left) + " < ";
                break;
            case LTE:        // this part assumes inner expression are a signature instances and are comparable
            case NOT_GT:
                res = this.genExpr(node.left) + " <= ";
                break;
            case GT:         // this part assumes inner expression are a signature instances and are comparable
            case NOT_LTE:
                res = this.genExpr(node.left) + " > ";
                break;
            case GTE:        // this part assumes inner expression are a signature instances and are comparable
            case NOT_LT:
                res = this.genExpr(node.left) + " >= ";
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
                res = this.genExpr(node.left) + " in ";
                break;
            case NOT_IN:        // this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left) + " not in ";
                break;
            case AND:           // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left) + ") and ";
                break;
            case OR:            // this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left) + ") or ";
                break;
            case IFF:
                res = "(" + this.genExpr(node.left) + ") == ";
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
            if(shouldAddParenthesis) {
                res += "(" + this.genExpr(node.right) + ")";
            }else{
                res += this.genExpr(node.right);
            }
        }
        return res;
    }

    private Variable getVarName(String varName) {
        Variable var = new Variable(varName);
        if (varName.contains("/")){
            String[] parts = varName.split("/");
            var.setGlobal(true);
            var.setName(parts[parts.length - 1]);
            varName = varName.replace("/", "_");
            var.setPrefix(varName.substring(0, varName.lastIndexOf("_") + 1));
            relatedDynamicVars.add(var);
        } else if (variable2StateNameMap.containsKey(varName)){
            var.setGlobal(true);
            var.setPrefix(variable2StateNameMap.get(varName) + "_");
            relatedDynamicVars.add(var);
        }
        return var;
    }

    // "SS." + "<State Name>" + "<Name>" + "_updated"
    public static class Variable{
        private boolean isGlobal = false;   // Add VarTrackerName if it is global
        private boolean hasSuffix = false;  // Add VarLocalSuffix if it is local
        private String prefix = "";
        private String name = "";

        public Variable(){}
        public Variable(String name){ this.name = name;}
        public String toString(){ return ((isGlobal)? VarTrackerName : "") + prefix + name + ((hasSuffix)? VarLocalSuffix : "");}
        public String getQualName(){ return this.toString(); }
        public String getName(){ return name; }
        public String getFullName(){ return prefix + name; }
        public String getLocalName(){ return prefix + name + VarLocalSuffix; }
        public void setPrefix(String prefix){this.prefix = prefix;}
        public void setName(String name){this.name = name;}
        public void setHasSuffix(boolean hasSuffix){this.hasSuffix = hasSuffix;}
        public void setGlobal(boolean isGlobal){this.isGlobal = isGlobal;}
        @Override
        public int hashCode() { return Objects.hash(prefix, name); }
        @Override
        public boolean equals(Object o) {
            if (this == o) { return true; }
            if (o == null || getClass() != o.getClass()) { return false; }
            Variable variable = (Variable) o;
            return Objects.equals(prefix, variable.prefix) &&
                    Objects.equals(name, variable.name);
        }
    }

    public static class VariableSet implements Iterable<Variable> {
        private final LinkedHashSet<Variable> vars = new LinkedHashSet<>();
        public VariableSet(){}
        public void add(Variable var){ vars.add(var); }
        public boolean checkIntersection(VariableSet other){return !Collections.disjoint(getFullNamesSet(), other.getFullNamesSet());}
        public List<String> getNames(){return vars.stream().map(Variable::getName).distinct().collect(Collectors.toList());}

        public List<String> getFullNames(){ return vars.stream().map(Variable::getFullName).distinct().collect(Collectors.toList()); }
        public Set<String> getFullNamesSet(){ return vars.stream().map(Variable::getFullName).collect(Collectors.toSet()); }

        @Override
        public Iterator<Variable> iterator() { return vars.iterator(); }
        @Override
        public void forEach(Consumer<? super Variable> action) { vars.forEach(action); }

        public boolean contains(Variable var) { return vars.contains(var); }
    }
}
