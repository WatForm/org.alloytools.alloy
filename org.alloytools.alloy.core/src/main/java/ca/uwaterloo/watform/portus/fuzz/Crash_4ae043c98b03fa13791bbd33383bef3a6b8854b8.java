import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class Crash_4ae043c98b03fa13791bbd33383bef3a6b8854b8 {
    static final String base64Bytes = String.join("", "rO0ABXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAAwdwQAAAAwc3IAEWphdmEubGFuZy5JbnRlZ2VyEuKgpPeBhzgCAAFJAAV2YWx1ZXhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cAAAAAFzcQB+AAIAAAAQc3EAfgACAAAAAnNyABFqYXZhLmxhbmcuQm9vbGVhbs0gcoDVnPruAgABWgAFdmFsdWV4cABzcQB+AAIAAAAAcQB+AAlzcQB+AAcBcQB+AApzcQB+AAIAAAAOc3EAfgACAAAAA3EAfgAFc3EAfgACAAAAB3EAfgAFcQB+AARxAH4ABXNxAH4AAgAAAARxAH4ABHEAfgAJc3EAfgACAAAAC3NxAH4AAgAAAApzcQB+AAIAAAANcQB+AAZxAH4ACnNxAH4AAgAAAhFzcQB+AAIAAAAncQB+AAxxAH4ABHEAfgAFcQB+AA1xAH4ABXEAfgANcQB+AAZxAH4ADHEAfgAEcQB+AAlxAH4ABHEAfgAJcQB+AARxAH4ACXEAfgAEcQB+AAlxAH4ACXEAfgAEcQB+AARxAH4ABHEAfgAJcQB+AAhzcQB+AAL/////eA==");

    public static void main(String[] args) throws Throwable {
        Crash_4ae043c98b03fa13791bbd33383bef3a6b8854b8.class.getClassLoader().setDefaultAssertionStatus(true);
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