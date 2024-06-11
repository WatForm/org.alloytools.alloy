package ca.uwaterloo.watform.portus.fuzz;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class Crash_bd172556396aefeb7c7ae0fd649b748e89e1145b {
    static final String base64Bytes = String.join("", "rO0ABXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAAPdwQAAAAPc3IAEWphdmEubGFuZy5JbnRlZ2VyEuKgpPeBhzgCAAFJAAV2YWx1ZXhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cAAAAABxAH4ABHNxAH4AAgAAAARzcQB+AAIAAAAGcQB+AAZzcQB+AAIAAAABc3EAfgACAAAAAnNyABFqYXZhLmxhbmcuQm9vbGVhbs0gcoDVnPruAgABWgAFdmFsdWV4cAFzcQB+AAL//+x4cQB+AAdxAH4AB3EAfgAHcQB+AARzcQB+AAkAc3EAfgAC/////3g=");

    public static void main(String[] args) throws Throwable {
        Crash_bd172556396aefeb7c7ae0fd649b748e89e1145b.class.getClassLoader().setDefaultAssertionStatus(true);
        try {
            Method fuzzerInitialize = ca.uwaterloo.watform.portus.fuzz.ASTFuzzTarget.class.getMethod("fuzzerInitialize");
            fuzzerInitialize.invoke(null);
        } catch (NoSuchMethodException ignored) {
            try {
                Method fuzzerInitialize = ca.uwaterloo.watform.portus.fuzz.ASTFuzzTarget.class.getMethod("fuzzerInitialize", String[].class);
                fuzzerInitialize.invoke(null, (Object) args);
            } catch (NoSuchMethodException ignored1) {
            } catch (IllegalAccessException | InvocationTargetException e) {
                e.printStackTrace();
                System.exit(1);
            }
        } catch (IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
            System.exit(1);
        }
        com.code_intelligence.jazzer.api.CannedFuzzedDataProvider input = new com.code_intelligence.jazzer.api.CannedFuzzedDataProvider(base64Bytes);
        ca.uwaterloo.watform.portus.fuzz.ASTFuzzTarget.fuzzerTestOneInput(input);
    }
}