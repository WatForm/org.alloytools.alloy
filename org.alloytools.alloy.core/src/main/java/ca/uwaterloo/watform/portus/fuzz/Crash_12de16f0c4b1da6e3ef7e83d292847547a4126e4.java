package ca.uwaterloo.watform.portus.fuzz;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class Crash_12de16f0c4b1da6e3ef7e83d292847547a4126e4 {
    static final String base64Bytes = String.join("", "rO0ABXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAAjdwQAAAAjc3IAEWphdmEubGFuZy5JbnRlZ2VyEuKgpPeBhzgCAAFJAAV2YWx1ZXhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cAAAAARzcQB+AAIAAAA1c3EAfgACAAAAN3NyABFqYXZhLmxhbmcuQm9vbGVhbs0gcoDVnPruAgABWgAFdmFsdWV4cABzcQB+AAIAAAAAcQB+AAlxAH4ACHNxAH4AAgAAAAFxAH4ACXEAfgAJcQB+AAlxAH4ACHEAfgAKcQB+AAlxAH4ACXEAfgAJcQB+AAhxAH4ACnEAfgAJcQB+AAlxAH4ACXEAfgAJcQB+AAlxAH4ACXEAfgAIcQB+AAhxAH4ACHEAfgAIcQB+AAhxAH4ACHEAfgAKcQB+AApxAH4ACXEAfgAIc3EAfgAC/////3g=");

    public static void main(String[] args) throws Throwable {
        Crash_12de16f0c4b1da6e3ef7e83d292847547a4126e4.class.getClassLoader().setDefaultAssertionStatus(true);
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