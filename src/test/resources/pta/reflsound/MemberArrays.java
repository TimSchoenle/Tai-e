import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;

/**
 * Option reflection-members: the member arrays of a known class and the
 * fields of a constant name.
 */
public class MemberArrays {

    public static void main(String[] args) throws Exception {
        declaredMethods();
        interfaceDefault();
        constructors();
        inheritedFields();
        inheritedField();
        declaredField();
    }

    static void declaredMethods() throws Exception {
        for (Method m : MaListed.class.getDeclaredMethods()) {
            m.invoke(new MaListed());
            PTAAssert.calls("<MaListed: void listed()>");
        }
    }

    static void interfaceDefault() throws Exception {
        for (Method m : MaImpl.class.getMethods()) {
            m.invoke(new MaImpl());
            PTAAssert.calls("<MaIface: void dflt()>");
        }
    }

    static void constructors() throws Exception {
        for (Constructor<?> c : MaMade.class.getConstructors()) {
            c.newInstance();
            PTAAssert.calls("<MaMade: void <init>()>");
        }
    }

    static void inheritedFields() throws Exception {
        MaDerived d = new MaDerived();
        for (Field f : MaDerived.class.getFields()) {
            f.set(d, new MaTask());
        }
        d.task.run();
        PTAAssert.calls("<MaTask: void run()>");
    }

    static void inheritedField() throws Exception {
        MaDerived d = new MaDerived();
        MaDerived.class.getField("task").set(d, new MaTask2());
        d.task.run();
        PTAAssert.calls("<MaTask2: void run()>");
    }

    static void declaredField() throws Exception {
        MaBase b = new MaBase();
        MaBase.class.getDeclaredField("task").set(b, new MaTask3());
        b.task.run();
        PTAAssert.calls("<MaTask3: void run()>");
    }
}

class MaListed {
    public void listed() {
    }
}

interface MaIface {
    default void dflt() {
    }
}

class MaImpl implements MaIface {
}

class MaMade {
    public MaMade() {
    }

    public MaMade(Object o) {
    }
}

class MaBase {
    public Runnable task;
}

class MaDerived extends MaBase {
}

class MaTask implements Runnable {
    public void run() {
    }
}

class MaTask2 implements Runnable {
    public void run() {
    }
}

class MaTask3 implements Runnable {
    public void run() {
    }
}
