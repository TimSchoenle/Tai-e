/**
 * A reflective call of a static method or a constructor and a reflective
 * access of a static field initialize the class, as the direct ones do.
 * No class here is used directly, so only the reflective use initializes it.
 */
public class ClassInit {

    public static void main(String[] args) throws Exception {
        staticMethod();
        constructor();
        staticFieldGet();
        staticFieldSet();
    }

    static void staticMethod() throws Exception {
        CiStatic.class.getMethod("get").invoke(null);
        PTAAssert.reachable("<CiStatic: void <clinit>()>");
    }

    static void constructor() throws Exception {
        CiMade.class.getConstructor().newInstance();
        PTAAssert.reachable("<CiMade: void <clinit>()>");
    }

    static void staticFieldGet() throws Exception {
        Runnable r = (Runnable) CiHolder.class.getField("task").get(null);
        r.run();
        PTAAssert.calls("<CiTask: void run()>");
    }

    static void staticFieldSet() throws Exception {
        CiSlot.class.getField("slot").set(null, new CiOther());
        PTAAssert.reachable("<CiSlot: void <clinit>()>");
    }
}

class CiStatic {
    static Object value;

    static {
        value = new Object();
    }

    public static Object get() {
        return value;
    }
}

class CiMade {
    static Object seen;

    static {
        seen = new Object();
    }

    public CiMade() {
    }
}

class CiHolder {
    public static Runnable task = new CiTask();
}

class CiTask implements Runnable {
    public void run() {
    }
}

class CiSlot {
    public static Runnable slot;

    static Object mark = new Object();
}

class CiOther implements Runnable {
    public void run() {
    }
}
