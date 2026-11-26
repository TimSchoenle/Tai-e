import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Method references whose receiver is a lambda object: each body method
 * named *Body or *Sink is reached only if the call through the method
 * reference reaches the lambda's target method with its arguments.
 */
public class LambdaReceiver {

    interface Marker {
        default void mark() {
            markBody();
        }
    }

    interface Sink {
        void sink();

        void returned();
    }

    static class BoundSink implements Sink {
        public void sink() {
            boundArgSink();
        }

        public void returned() {
            boundReturnSink();
        }
    }

    static class UnboundSink implements Sink {
        public void sink() {
            unboundArgSink();
        }

        public void returned() {
            unboundReturnSink();
        }
    }

    static class Holder {
        void hold() {
            holderBody();
        }
    }

    static class Made {
        Made() {
            ctorBody();
        }
    }

    static Runnable cycleA;

    static Runnable cycleB;

    public static void main(String[] args) {
        bound();
        unbound();
        nested();
        lambdaOfMethodRef();
        markerDefault();
        arguments();
        targets();
        cycle();
    }

    static void bound() {
        Runnable r1 = () -> boundBody();
        Runnable r2 = r1::run;
        r2.run();
    }

    static void unbound() {
        Runnable r1 = () -> unboundBody();
        Consumer<Runnable> c = Runnable::run;
        c.accept(r1);
    }

    static void nested() {
        Runnable r1 = () -> nestedBody();
        Runnable r2 = r1::run;
        Runnable r3 = r2::run;
        r3.run();
    }

    static void lambdaOfMethodRef() {
        Runnable r1 = () -> lambdaOfRefBody();
        Runnable r2 = r1::run;
        Runnable r3 = () -> r2.run();
        r3.run();
    }

    static void markerDefault() {
        Runnable m = (Runnable & Marker) () -> markerSamBody();
        Runnable mark = ((Marker) m)::mark;
        mark.run();
        Runnable sam = m::run;
        sam.run();
    }

    static void arguments() {
        // one lambda per path, so that no path passes on the other's object
        Function<Sink, Object> f1 = s -> {
            s.sink();
            return s;
        };
        Function<Sink, Object> g = f1::apply;
        ((Sink) g.apply(new BoundSink())).returned();
        Function<Sink, Object> f2 = s -> {
            s.sink();
            return s;
        };
        BiFunction<Function<Sink, Object>, Sink, Object> h = Function::apply;
        ((Sink) h.apply(f2, new UnboundSink())).returned();
    }

    static void targets() {
        Runnable sr = LambdaReceiver::staticBody;
        Runnable sr2 = sr::run;
        sr2.run();
        Runnable ir = new Holder()::hold;
        Runnable ir2 = ir::run;
        ir2.run();
        Supplier<Object> ctor = Made::new;
        Supplier<Object> ctor2 = ctor::get;
        ctor2.get();
    }

    static void cycle() {
        // m1's receiver is m2, m2's receivers are m1 (the cycle) and the
        // lambda, and nothing else calls m2 or the lambda: cycleBody is
        // reached only along m1 -> m2 -> lambda, through the cycle
        Runnable m1 = cycleA::run;
        Runnable m2 = cycleB::run;
        cycleA = m2;
        cycleB = m1;
        cycleB = () -> cycleBody();
        m1.run();
    }

    static void boundBody() {
    }

    static void unboundBody() {
    }

    static void nestedBody() {
    }

    static void lambdaOfRefBody() {
    }

    static void markBody() {
    }

    static void markerSamBody() {
    }

    static void boundArgSink() {
    }

    static void boundReturnSink() {
    }

    static void unboundArgSink() {
    }

    static void unboundReturnSink() {
    }

    static void staticBody() {
    }

    static void holderBody() {
    }

    static void ctorBody() {
    }

    static void cycleBody() {
    }
}
