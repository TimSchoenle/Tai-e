import java.io.Serializable;
import java.lang.reflect.Method;
import java.util.function.Consumer;

/**
 * Lambda objects of altMetafactory: their classes implement the interfaces
 * the flags add (Serializable, the markers), so they pass casts, array stores,
 * typed lambda parameters and reflective arguments of those interfaces, and a
 * default method of a marker runs on them. Each path ends in a call of its
 * own static method, whose reachability the test asserts. The paths named
 * neg* must stay unreached: the object does not implement Other at run time,
 * a plain metafactory lambda does not implement Serializable, and a lambda
 * object's own interface method shadows a default method of the same
 * signature in a superinterface.
 */
class LambdaAddedInterfaces {

    interface Marker {
        default void mark() {
            markBody();
        }
    }

    interface Other {
    }

    interface Base {
        default void act() {
            negBaseBody();
        }
    }

    interface Act extends Base {
        @Override
        void act();
    }

    public static void main(String[] args) throws Exception {
        cast();
        arrayStore();
        lambdaParameter();
        reflectiveArgument();
        markerDefault();
        negOtherCast();
        negOtherArrayStore();
        negPlainLambda();
        shadowedDefault();
        plainShadowedDefault();
        bridge();
    }

    interface Taker<T> {
        void take(T t);
    }

    interface StringTaker extends Taker<String> {
        @Override
        void take(String s);
    }

    static void plainShadowedDefault() {
        Act act = () -> plainActBody();
        act.act();
    }

    @SuppressWarnings("unchecked")
    static void bridge() {
        Object lambda = (StringTaker & Serializable) s -> bridgeBody();
        ((Taker<String>) lambda).take("x");
    }

    static void cast() {
        Object o = (Runnable & Serializable) () -> castBody();
        Serializable s = (Serializable) o;
        ((Runnable) s).run();
    }

    static void arrayStore() {
        Object lambda = (Runnable & Serializable) () -> storeBody();
        Object[] array = new Serializable[1];
        array[0] = lambda;
        ((Runnable) array[0]).run();
    }

    static void lambdaParameter() {
        Object lambda = (Runnable & Serializable) () -> parameterBody();
        Consumer<Serializable> sink = s -> ((Runnable) s).run();
        @SuppressWarnings("unchecked")
        Consumer<Object> raw = (Consumer<Object>) (Consumer<?>) sink;
        raw.accept(lambda);
    }

    static void reflectiveArgument() throws Exception {
        Object lambda = (Runnable & Serializable) () -> reflectiveBody();
        Method target = LambdaAddedInterfaces.class.getDeclaredMethod(
                "reflectiveTarget", Serializable.class);
        target.invoke(null, lambda);
    }

    static void reflectiveTarget(Serializable s) {
        ((Runnable) s).run();
    }

    static void markerDefault() {
        Object lambda = (Runnable & Marker) () -> { };
        ((Marker) lambda).mark();
    }

    static void negOtherCast() {
        Object lambda = (Runnable & Marker) () -> negCastBody();
        if (args() > 0) {
            Other other = (Other) lambda;
            ((Runnable) other).run();
        }
    }

    static void negOtherArrayStore() {
        Object lambda = (Runnable & Serializable) () -> negStoreBody();
        Object[] array = new Other[1];
        if (args() > 0) {
            array[0] = lambda;
            ((Runnable) array[0]).run();
        }
    }

    static void negPlainLambda() {
        Runnable plain = () -> negPlainBody();
        Object o = plain;
        if (args() > 0) {
            ((Runnable) (Serializable) o).run();
        }
    }

    static void shadowedDefault() {
        Act act = (Act & Serializable) () -> actBody();
        act.act();
    }

    static int args() {
        return 1;
    }

    static void castBody() {
    }

    static void storeBody() {
    }

    static void parameterBody() {
    }

    static void reflectiveBody() {
    }

    static void markBody() {
    }

    static void actBody() {
    }

    static void plainActBody() {
    }

    static void bridgeBody() {
    }

    static void negCastBody() {
    }

    static void negStoreBody() {
    }

    static void negPlainBody() {
    }

    static void negBaseBody() {
    }
}
