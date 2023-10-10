package ca.uwaterloo.watform.portus.fuzz;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class Crash_1ca16510e343393f4447e0ce2c0f35c82c88ba18 {
    static final String base64Bytes = String.join("", "rO0ABXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAAKdwQAAAAKc3IAEWphdmEubGFuZy5JbnRlZ2VyEuKgpPeBhzgCAAFJAAV2YWx1ZXhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cAAAAABxAH4ABHNxAH4AAgAAAARzcQB+AAIAAAABcQB+AAZzcQB+AAIAAAAKcQB+AARzcQB+AAL/////c3IAEWphdmEubGFuZy5Cb29sZWFuzSBygNWc+u4CAAFaAAV2YWx1ZXhwAXEAfgAIeA==");

    public static void main(String[] args) throws Throwable {
        Crash_1ca16510e343393f4447e0ce2c0f35c82c88ba18.class.getClassLoader().setDefaultAssertionStatus(true);
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