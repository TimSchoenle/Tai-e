import java.io.Serializable;

/**
 * Reflective targets ruled out by the arguments a call passes: only a
 * target the JVM refuses before it runs (an argument the parameter type
 * does not admit after unboxing, null for a primitive parameter, a
 * constructor of an abstract class) is dropped; a target that may run
 * stays.
 */
public class ArgTypes {

    static final String INVOKE =
            "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>";

    static final String NEW_INSTANCE =
            "<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>";

    static final String RUN_ACTION = "<AtPriv: java.lang.Object run(AtAction)>";

    static final String RUN_EXC_ACTION = "<AtPriv: java.lang.Object run(AtExcAction)>";

    static final String CALLOC_STACK = "<AtVk: java.lang.Object calloc(AtStack)>";

    static final String CALLOC_INT = "<AtVk: java.lang.Object calloc(int)>";

    public static void main(String[] args) throws Exception {
        lambdaOverload();
        anonymousOverload();
        markerLambda();
        serializableLambda();
        lambdaFromParam(() -> "p");
        nullReference();
        stackOverload(new AtStack());
        boxedArgument();
        shortBox();
        nullForPrimitive();
        unstoredElement();
        reflectiveBox();
        branchedStore(args.length);
        lastStoreWins();
        storeAfterCall();
        interfaceTyped(Integer.valueOf(2));
        abstractClassNewInstance(args.length);
        argumentOrder();
        constructorArgument();
        abstractConstructor(args.length);
    }

    /** The doPrivileged shape: a lambda of one interface never matches the other. */
    static Object lambdaOverload() throws Exception {
        AtExcAction action = () -> "x";
        Object r = Class.forName("AtPriv").getMethod("run", AtExcAction.class).invoke(null, action);
        PTAAssert.callsExact(INVOKE, RUN_EXC_ACTION);
        return r;
    }

    static Object anonymousOverload() throws Exception {
        AtExcAction action = new AtExcAction() {
            @Override
            public Object run() {
                return "y";
            }
        };
        Object r = AtPriv.class.getMethod("run", AtExcAction.class).invoke(null, action);
        PTAAssert.callsExact(INVOKE, RUN_EXC_ACTION);
        return r;
    }

    /** An intersection cast: the value is no plain lambda definition, every overload stays. */
    static void markerLambda() throws Exception {
        AtExcAction action = (AtExcAction & AtMarker) () -> "m";
        AtPriv.class.getMethod("mark", AtMarker.class).invoke(null, action);
        PTAAssert.callsExact(INVOKE, "<AtPriv: void mark(AtMarker)>",
                "<AtPriv: void mark(java.io.Serializable)>", "<AtPriv: void mark(AtBase)>");
    }

    /**
     * A serializable lambda comes from altMetafactory, which may add marker
     * interfaces: every interface overload stays, a class one does not.
     */
    static void serializableLambda() throws Exception {
        AtSerAction action = () -> "s";
        AtPriv.class.getMethod("mark", AtMarker.class).invoke(null, action);
        PTAAssert.callsExact(INVOKE, "<AtPriv: void mark(AtMarker)>",
                "<AtPriv: void mark(java.io.Serializable)>");
    }

    /** A parameter may be null: every reference overload stays. */
    static Object lambdaFromParam(AtExcAction action) throws Exception {
        Object r = AtPriv.class.getMethod("run", AtExcAction.class).invoke(null, action);
        PTAAssert.callsExact(INVOKE, RUN_ACTION, RUN_EXC_ACTION);
        return r;
    }

    static Object nullReference() throws Exception {
        Object r = AtPriv.class.getMethod("run", AtExcAction.class).invoke(null, (Object) null);
        PTAAssert.callsExact(INVOKE, RUN_ACTION, RUN_EXC_ACTION);
        return r;
    }

    /** The VulkanPNextStruct shape: a MemoryStack never unboxes to int. */
    static Object stackOverload(AtStack stack) throws Exception {
        Object r = AtVk.class.getMethod("calloc", AtStack.class).invoke(null, stack);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK);
        return r;
    }

    static Object boxedArgument() throws Exception {
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, 5);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    static Object shortBox() throws Exception {
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, (short) 3);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    static Object nullForPrimitive() throws Exception {
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, (Object) null);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK);
        return r;
    }

    static Object unstoredElement() throws Exception {
        Object[] a = new Object[1];
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, a);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK);
        return r;
    }

    /**
     * The box of a primitive that reflection returns is no object of the
     * analysis; the argument is typed Object, so calloc(int) stays.
     */
    static Object reflectiveBox() throws Exception {
        Object n = AtVk.class.getMethod("size").invoke(null);
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, n);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    /** A store on one branch only: the look gives up, both stay. */
    static Object branchedStore(int n) throws Exception {
        Object[] a = new Object[1];
        if (n > 0) {
            a[0] = new AtStack();
        }
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, a);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    /** The last store to an index is the element: the Integer, not the AtStack. */
    static Object lastStoreWins() throws Exception {
        Object[] a = new Object[1];
        a[0] = new AtStack();
        a[0] = Integer.valueOf(4);
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, a);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    /** A store after the call: the look gives up, both stay. */
    static Object storeAfterCall() throws Exception {
        Object[] a = new Object[1];
        a[0] = new AtStack();
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, a);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        a[0] = r;
        return r;
    }

    /** An interface type may hold a box: calloc(int) stays. */
    static Object interfaceTyped(Comparable<?> value) throws Exception {
        Object r = AtVk.class.getMethod("calloc", int.class).invoke(null, value);
        PTAAssert.callsExact(INVOKE, CALLOC_STACK, CALLOC_INT);
        return r;
    }

    @SuppressWarnings("deprecation")
    static Object abstractClassNewInstance(int n) throws Exception {
        Class<?> k = n > 5 ? AtChannel.class : AtAbstractBuf.class;
        Object c = k.newInstance();
        PTAAssert.callsExact("<java.lang.Class: java.lang.Object newInstance()>",
                "<AtChannel: void <init>()>");
        return c;
    }

    static void argumentOrder() throws Exception {
        AtVk.class.getMethod("pairs", AtStack.class, int.class).invoke(null, new AtStack(), 7);
        PTAAssert.callsExact(INVOKE, "<AtVk: void pairs(AtStack,int)>");
    }

    static Object constructorArgument() throws Exception {
        Object h = AtHolder.class.getConstructor(AtStack.class).newInstance(new AtStack());
        PTAAssert.callsExact(NEW_INSTANCE, "<AtHolder: void <init>(AtStack)>");
        return h;
    }

    /**
     * The ReflectiveChannelFactory shape: newInstance of an abstract class
     * throws before any constructor runs; the other constructors stay
     * whatever the result is cast to.
     */
    static Object abstractConstructor(int n) throws Exception {
        Class<?> k = n > 5 ? AtChannel.class : n > 3 ? AtAbstractBuf.class : AtHandler.class;
        Object c = k.getConstructor().newInstance();
        PTAAssert.callsExact(NEW_INSTANCE, "<AtChannel: void <init>()>", "<AtHandler: void <init>()>");
        return c;
    }
}

interface AtAction {
    Object run();
}

interface AtExcAction {
    Object run() throws Exception;
}

interface AtMarker {
}

interface AtSerAction extends AtExcAction, Serializable {
}

class AtBase {
}

class AtStack {
}

class AtPriv {

    public static Object run(AtAction action) {
        return action.run();
    }

    public static Object run(AtExcAction action) throws Exception {
        return action.run();
    }

    public static void mark(AtMarker marker) {
    }

    public static void mark(Serializable serializable) {
    }

    public static void mark(AtBase base) {
    }
}

class AtVk {

    public static Object calloc(AtStack stack) {
        return stack;
    }

    public static Object calloc(int n) {
        return new Object[n];
    }

    public static int size() {
        return 3;
    }

    public static void pairs(AtStack stack, int n) {
    }

    public static void pairs(int n, AtStack stack) {
    }
}

class AtHolder {

    public AtHolder(AtStack stack) {
    }

    public AtHolder(int n) {
    }
}

class AtChannel {

    public AtChannel() {
    }
}

abstract class AtAbstractBuf {

    public AtAbstractBuf() {
    }
}

class AtHandler {

    public AtHandler() {
    }
}
