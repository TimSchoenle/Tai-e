import java.lang.reflect.Field;
import java.lang.reflect.Method;

/**
 * Lazy reflection members at the getters with a name argument, mixed: at
 * N=1 the first receiver class (LnA) stays eager, the second (LnB) reaches
 * the receiver late and is taken lazily, and a second name reaches the name
 * argument later still, so the call site's eager classes and its placeholder
 * both grow by that name.
 */
public class LazyNamed {

    static Class<?> klass = LnA.class;

    static String name = "a";

    static Class<?> fieldClass = LnA.class;

    static String fieldName = "fa";

    public static void main(String[] args) throws Exception {
        methods();
        fields();
    }

    /**
     * LnA.a() brings LnB.class, LnB.a() brings the name "b": LnA.b() is
     * concrete (old class, new name), LnB.b() comes from the placeholder.
     */
    static void methods() throws Exception {
        Method m = klass.getDeclaredMethod(name);
        Object next = m.invoke(null);
        PTAAssert.calls("<LnA: java.lang.Object a()>", "<LnB: java.lang.Object a()>",
                "<LnA: java.lang.Object b()>", "<LnB: java.lang.Object b()>");
        if (next instanceof Class) {
            klass = (Class<?>) next;
        } else {
            name = (String) next;
        }
    }

    /**
     * LnA.fa holds LnB.class, LnB.fa the name "fb": the store reaches LnA.fb
     * (concrete) and LnB.fb (from the placeholder).
     */
    static void fields() throws Exception {
        Field f = fieldClass.getDeclaredField(fieldName);
        Object value = f.get(null);
        f.set(null, new LnTask());
        if (value instanceof Class) {
            fieldClass = (Class<?>) value;
        } else {
            fieldName = (String) value;
        }
        LnA.fb.run();
        PTAAssert.calls("<LnTask: void run()>");
        LnB.fb.run();
        PTAAssert.calls("<LnTask: void run()>");
    }
}

class LnA {

    static Object fa = LnB.class;

    static Runnable fb;

    static Object a() {
        return LnB.class;
    }

    static Object b() {
        return null;
    }
}

class LnB {

    static Object fa = "fb";

    static Runnable fb;

    static Object a() {
        return "b";
    }

    static Object b() {
        return null;
    }
}

class LnTask implements Runnable {

    public void run() {
    }
}
