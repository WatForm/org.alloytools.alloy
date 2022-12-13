package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashTemplateCall extends DashSuperAST {
    private String       templateName  = "";
    private List<String> templateParam = new ArrayList<String>();

    public DashTemplateCall(Pos pos, String name, String templateName, List<ExprVar> templateParam) {
    	super(pos, name);
        this.setTemplateName(templateName);

        for (ExprVar var : templateParam) {
            this.getTemplateParam().add(var.toString());
        }
    }

	public String getTemplateName() {
		return templateName;
	}

	public void setTemplateName(String templateName) {
		this.templateName = templateName;
	}

	public List<String> getTemplateParam() {
		return templateParam;
	}

	public void setTemplateParam(List<String> templateParam) {
		this.templateParam = templateParam;
	}
}
