import java.lang.reflect.Method;

/**
 * Option reflection-members-lazy: a value stored into a field of one member
 * object is loaded from another member object of the same member
 * (LazyFieldsPlugin models LfSink). With lazy members the two are different
 * placeholders, so only the shared member object fields carry the value.
 */
public class LazyFields {

    public static void main(String[] args) throws Exception {
        Method a = LfOwner.class.getDeclaredMethod("t");
        LfSink.store(a, new LfTask());
        Method b = LfOwner.class.getDeclaredMethods()[0];
        Runnable r = (Runnable) LfSink.load(b);
        r.run();
        PTAAssert.calls("<LfTask: void run()>");
    }
}

class LfOwner {
    static void t() {
    }
}

class LfSink {
    Object cell;

    static void store(Method m, Object v) {
    }

    /** Returns m too, so that the return variable is not null alone. */
    static Object load(Method m) {
        return m;
    }
}

class LfTask implements Runnable {
    public void run() {
    }
}
