/**
 * Class.getMethod(name) finds the public methods of the superinterfaces
 * too: a default method, an abstract one an abstract class leaves to its
 * subclasses, and one of the superinterface of an interface.
 */
public class GetMethodIface {

    public static void main(String[] args) throws Exception {
        defaultMethod();
        abstractMethod();
        superinterfaceOfInterface();
        overridden();
    }

    static void defaultMethod() throws Exception {
        GmImpl.class.getMethod("dflt").invoke(new GmImpl());
        PTAAssert.calls("<GmIface: void dflt()>");
    }

    static void abstractMethod() throws Exception {
        GmAbstract.class.getMethod("abs").invoke(new GmConcrete());
        PTAAssert.calls("<GmConcrete: void abs()>");
    }

    static void superinterfaceOfInterface() throws Exception {
        GmSub.class.getMethod("top").invoke(new GmBoth());
        PTAAssert.calls("<GmBoth: void top()>");
    }

    static void overridden() throws Exception {
        GmOverride.class.getMethod("dflt").invoke(new GmOverride());
        PTAAssert.callsExact(TypeMatch.INVOKE, "<GmOverride: void dflt()>");
    }
}

interface GmIface {
    default void dflt() {
    }
}

class GmImpl implements GmIface {
}

interface GmAbs {
    void abs();
}

abstract class GmAbstract implements GmAbs {
}

class GmConcrete extends GmAbstract {
    public void abs() {
    }
}

interface GmTop {
    void top();
}

interface GmSub extends GmTop {
}

class GmBoth implements GmSub {
    public void top() {
    }
}

class GmOverride implements GmIface {
    public void dflt() {
    }
}
