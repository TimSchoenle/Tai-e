import java.lang.annotation.Annotation;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;

/**
 * Option reflection-members-lazy: the member set of a placeholder grows
 * after its consumers took it, a consumer takes it after its members came,
 * and every consumer of member objects reads the members of a placeholder.
 */
public class LazyGrowth {

    static Class<?> klass = LgFirst.class;

    static String name = "first";

    static String fieldName = "f1";

    static Method saved;

    public static void main(String[] args) throws Exception {
        receiverGrows();
        nameGrows();
        lateConsumer();
        overlapping(args);
        declaringClass();
        constructor();
        parameterAnnotations();
        fieldNameGrows();
    }

    /** LgSecond.class reaches the receiver only through the call of LgFirst.next(). */
    static void receiverGrows() throws Exception {
        for (Method m : klass.getDeclaredMethods()) {
            Object next = m.invoke(null);
            PTAAssert.calls("<LgFirst: java.lang.Class next()>", "<LgSecond: java.lang.Class last()>");
            klass = (Class<?>) next;
        }
    }

    /** The name "second" reaches getDeclaredMethod only through the call of LgNamed.first(). */
    static void nameGrows() throws Exception {
        Method m = LgNamed.class.getDeclaredMethod(name);
        Object next = m.invoke(null);
        PTAAssert.calls("<LgNamed: java.lang.String first()>", "<LgNamed: java.lang.String second()>");
        name = (String) next;
    }

    /** The call in LgLate.go() takes the members only after all of them came. */
    static void lateConsumer() throws Exception {
        for (Method m : LgLate.class.getDeclaredMethods()) {
            saved = m;
            m.invoke(null);
            PTAAssert.calls("<LgLate: void go()>", "<LgLate: void target()>");
        }
    }

    /** Two placeholders that hold the same member reach one call. */
    static void overlapping(String[] args) throws Exception {
        Method m = LgOver.class.getMethod("x");
        if (args.length > 0) {
            m = LgOver.class.getDeclaredMethods()[0];
        }
        m.invoke(new LgOver());
        PTAAssert.calls("<LgOver: void x()>");
    }

    static void declaringClass() throws Exception {
        Method m = LgDecl.class.getDeclaredMethod("a");
        Class<?> c = m.getDeclaringClass();
        Method b = c.getDeclaredMethod("b");
        b.invoke(null);
        PTAAssert.calls("<LgDecl: void b()>");
    }

    static void constructor() throws Exception {
        Constructor<?> k = LgMade.class.getDeclaredConstructor();
        k.newInstance();
        PTAAssert.calls("<LgMade: void <init>()>");
    }

    static void parameterAnnotations() throws Exception {
        Method m = LgAnnotated.class.getDeclaredMethod("p", Object.class);
        Annotation[][] annotations = m.getParameterAnnotations();
        PTAAssert.notEmpty(annotations);
    }

    /** The field name "f2" reaches getDeclaredField only through the value of LgFields.f1. */
    static void fieldNameGrows() throws Exception {
        Field f = LgFields.class.getDeclaredField(fieldName);
        Object value = f.get(null);
        f.set(null, new LgTask());
        fieldName = (String) value;
        LgFields.f2.run();
        PTAAssert.calls("<LgTask: void run()>");
    }
}

class LgFirst {
    static Class<?> next() {
        return LgSecond.class;
    }
}

class LgSecond {
    static Class<?> last() {
        return null;
    }
}

class LgNamed {
    static String first() {
        return "second";
    }

    static String second() {
        return null;
    }

    static void unnamed() {
    }
}

class LgLate {
    static void go() throws Exception {
        LazyGrowth.saved.invoke(null);
        PTAAssert.calls("<LgLate: void go()>", "<LgLate: void target()>");
    }

    static void target() {
    }
}

class LgOver {
    public void x() {
    }
}

class LgDecl {
    static void a() {
    }

    static void b() {
    }
}

class LgMade {
    LgMade() {
    }

    LgMade(String s) {
    }
}

@Retention(RetentionPolicy.RUNTIME)
@interface LgAnno {
}

class LgAnnotated {
    void p(@LgAnno Object o) {
    }
}

class LgFields {
    static Object f1 = "f2";

    static Runnable f2;
}

class LgTask implements Runnable {
    public void run() {
    }
}
