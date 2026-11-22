import java.lang.reflect.Method;

/**
 * A taint object reaches a sink through the argument array of a reflective
 * call, so it passes the relay of the argument variable.
 */
class ReflectiveArgTaint {

    public static void main(String[] args) throws Exception {
        Method m = ReflectiveArgTaint.class.getMethod("leak", String.class);
        m.invoke(null, new Object[]{SourceSink.source()}); // taint
    }

    public static void leak(String s) {
        SourceSink.sink(s);
    }
}
