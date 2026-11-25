import java.lang.reflect.Method;

/**
 * Reflective targets that run must stay targets: neither a cast of the
 * result nor the static type of an argument rules one out; a known
 * argument count does (argument types the JVM refuses: ArgTypes).
 */
public class TypeMatch {

    /** The library edge of every Method.invoke call site, besides its reflective targets. */
    static final String INVOKE =
            "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>";

    public static void main(String[] args) throws Exception {
        castResult();
        boxedResult();
        laterCast();
        objectArgument();
        castConstruction();
        widenedArgument();
        argumentCount();
        nullArgs();
        paramArgs(new Object[0]);
        twoBranchArgs(args.length);
    }

    static String castResult() throws Exception {
        String s = (String) TmTarget.class.getMethod("anyValue").invoke(new TmTarget());
        PTAAssert.calls("<TmTarget: java.lang.Object anyValue()>");
        return s;
    }

    static Integer boxedResult() throws Exception {
        Integer i = (Integer) TmTarget.class.getMethod("size").invoke(new TmTarget());
        PTAAssert.calls("<TmTarget: int size()>");
        return i;
    }

    static String laterCast() throws Exception {
        Object r = TmTarget.class.getMethod("sideEffect").invoke(new TmTarget());
        PTAAssert.calls("<TmTarget: void sideEffect()>");
        if (r instanceof String) {
            return (String) r;
        }
        return null;
    }

    static Object text() {
        return "text";
    }

    static void objectArgument() throws Exception {
        TmTarget.class.getMethod("take", String.class).invoke(new TmTarget(), text());
        PTAAssert.calls("<TmTarget: void take(java.lang.String)>");
    }

    static Runnable castConstruction() throws Exception {
        Runnable r = (Runnable) TmTarget.class.getDeclaredConstructor().newInstance();
        PTAAssert.calls("<TmTarget: void <init>()>");
        return r;
    }

    static void widenedArgument() throws Exception {
        TmTarget.class.getMethod("takeLong", long.class).invoke(new TmTarget(), Integer.valueOf(1));
        PTAAssert.calls("<TmTarget: void takeLong(long)>");
    }

    static void argumentCount() throws Exception {
        TmTarget.class.getMethod("pair").invoke(new TmTarget());
        PTAAssert.callsExact(INVOKE, "<TmTarget: void pair()>");
    }

    static void nullArgs() throws Exception {
        TmTarget.class.getMethod("pair").invoke(new TmTarget(), (Object[]) null);
        PTAAssert.callsExact(INVOKE, "<TmTarget: void pair()>");
    }

    static void paramArgs(Object[] a) throws Exception {
        TmTarget.class.getMethod("pair").invoke(new TmTarget(), a);
        PTAAssert.calls("<TmTarget: void pair()>",
                "<TmTarget: void pair(java.lang.Object,java.lang.Object)>");
    }

    static void twoBranchArgs(int n) throws Exception {
        Object[] a;
        if (n > 0) {
            a = new Object[0];
        } else {
            a = new Object[]{"x", "y"};
        }
        TmTarget.class.getMethod("pair").invoke(new TmTarget(), a);
        PTAAssert.calls("<TmTarget: void pair()>",
                "<TmTarget: void pair(java.lang.Object,java.lang.Object)>");
    }
}

class TmTarget {

    public TmTarget() {
    }

    public Object anyValue() {
        return "value";
    }

    public int size() {
        return 1;
    }

    public void sideEffect() {
    }

    public void take(String text) {
    }

    public void takeLong(long value) {
    }

    public void pair() {
    }

    public void pair(Object first, Object second) {
    }
}
