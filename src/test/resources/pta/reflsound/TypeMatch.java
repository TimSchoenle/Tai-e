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
        unrelatedCast();
        objectParameter("text");
        objectField();
        interfaceArgument("text");
        unrelatedClassArgument(new TmOtherTask());
        numberToPrimitive(Integer.valueOf(2));
        constructorObjectArgument();
    }

    /** The target runs before the cast fails: a cast unrelated to its return type keeps it. */
    static Integer unrelatedCast() throws Exception {
        Integer i = (Integer) TmTarget.class.getMethod("label").invoke(new TmTarget());
        PTAAssert.calls("<TmTarget: java.lang.String label()>");
        return i;
    }

    /** A parameter typed Object may hold a String. */
    static void objectParameter(Object value) throws Exception {
        TmTarget.class.getMethod("take", String.class).invoke(new TmTarget(), value);
        PTAAssert.calls("<TmTarget: void take(java.lang.String)>");
    }

    static Object objectValue = "text";

    /** A field typed Object may hold a String. */
    static void objectField() throws Exception {
        TmTarget.class.getMethod("take", String.class).invoke(new TmTarget(), objectValue);
        PTAAssert.calls("<TmTarget: void take(java.lang.String)>");
    }

    /** A value typed by an interface the parameter class implements may be of that class. */
    static void interfaceArgument(CharSequence value) throws Exception {
        TmTarget.class.getMethod("take", String.class).invoke(new TmTarget(), value);
        PTAAssert.calls("<TmTarget: void take(java.lang.String)>");
    }

    /** A subclass of the declared class may implement the parameter's interface. */
    static void unrelatedClassArgument(TmOther value) throws Exception {
        TmTarget.class.getMethod("run", Runnable.class).invoke(new TmTarget(), value);
        PTAAssert.calls("<TmTarget: void run(java.lang.Runnable)>");
    }

    /** A value typed Number may be a box that invoke unboxes and widens. */
    static void numberToPrimitive(Number value) throws Exception {
        TmTarget.class.getMethod("takeLong", long.class).invoke(new TmTarget(), value);
        PTAAssert.calls("<TmTarget: void takeLong(long)>");
    }

    /** Constructor.newInstance admits a wider argument the same way. */
    static Object constructorObjectArgument() throws Exception {
        Object named = TmNamed.class.getConstructor(String.class).newInstance(text());
        PTAAssert.calls("<TmNamed: void <init>(java.lang.String)>");
        return named;
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

    public String label() {
        return "label";
    }

    public void run(Runnable task) {
    }
}

class TmOther {
}

class TmOtherTask extends TmOther implements Runnable {

    @Override
    public void run() {
    }
}

class TmNamed {

    public TmNamed(String name) {
    }
}
