package ca.uwaterloo.watform.transform;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import ca.uwaterloo.watform.rapidDash.RapidDashOptions;
import edu.mit.csail.sdg.translator.A4Solution;
import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.VelocityEngine;
import org.apache.velocity.runtime.RuntimeConstants;
import org.apache.velocity.runtime.resource.loader.ClasspathResourceLoader;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;

import java.util.stream.Collectors;

public class CoreDashToPython {
    static DashPythonTranslation dashPythonTranslation;

    public static DashPythonTranslation convertToPythonTranslation(DashModule module, A4Solution ans) {
        return new DashPythonTranslation(module, ans);
    }

    /**
     * Print to the standard output (command line)
     */
    public static void print(DashPythonTranslation dashPythonTranslation){
        System.out.println(convert2String(dashPythonTranslation));
    }

    /**
     * Output to the file indicated in RapidDashOptions
     */
    public static void toFile(DashPythonTranslation dashPythonTranslation) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(RapidDashOptions.outputDir + ".py"));
        writer.write(convert2String(dashPythonTranslation));
        writer.close();
    }

    public static String convert2String(DashPythonTranslation dashPythonTranslation) {
        // create velocity objects necessary for translation
        VelocityEngine ve = new VelocityEngine();
        ve.setProperty(RuntimeConstants.RESOURCE_LOADERS, "classpath");
        ve.setProperty("resource.loader.classpath.class", ClasspathResourceLoader.class.getName());
        ve.init();
        Template t = ve.getTemplate("templates/TestTemplateFile.vm");     // the template used to develop (without code that's not generated)
        VelocityContext vc = new VelocityContext();

        // add to template file

        // add signatures
        vc.put("signatures", dashPythonTranslation.signatures);
        vc.put("signaturesList", "[" + String.join(", ", dashPythonTranslation.signatures.stream().map(sig -> sig.getName()).collect(Collectors.toList())) + "]");

        // add relations
        vc.put("relations", dashPythonTranslation.relations);

        // add states
        vc.put("rootStates", dashPythonTranslation.getRootStates());
        vc.put("allStates", dashPythonTranslation.getAllStates());
        
        // add events
        vc.put("allEnvEvents", dashPythonTranslation.allEnvEvents);
        
        vc.put("rootState", dashPythonTranslation.rootState);

        // print modified template file
        StringWriter sw = new StringWriter();
        t.merge(vc, sw);
        return sw.toString();
    }
}
