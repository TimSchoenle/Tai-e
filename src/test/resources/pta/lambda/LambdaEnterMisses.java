import java.util.function.Function;

/**
 * Three method references of unrelated targets without captures, invoked
 * interleaved on one receiver variable of type Object, so that most pairs
 * of receiver type and target do not dispatch. Each callee stores the next
 * object into the field the receiver is read from, so new objects reach the
 * receiver variable after the invocations are known.
 */
public class LambdaEnterMisses {

    static Object holder;

    @SuppressWarnings("unchecked")
    public static void main(String[] args) {
        holder = new Red();
        Function<Object, Object> f = (Function<Object, Object>) (Function<?, ?>)
                (Function<Red, Object>) Red::paint;
        Function<Object, Object> g = (Function<Object, Object>) (Function<?, ?>)
                (Function<Green, Object>) Green::paint;
        Function<Object, Object> h = (Function<Object, Object>) (Function<?, ?>)
                (Function<Paintable, Object>) Paintable::paint;
        Object x = holder;
        f.apply(x);
        g.apply(x);
        h.apply(x);
        f.apply(x);
        g.apply(x);
    }
}

interface Paintable {
    Object paint();
}

class Red implements Paintable {

    public Object paint() {
        LambdaEnterMisses.holder = new Green();
        return this;
    }
}

class Green implements Paintable {

    public Object paint() {
        LambdaEnterMisses.holder = new Blue();
        return this;
    }
}

class Blue implements Paintable {

    public Object paint() {
        LambdaEnterMisses.holder = new int[0];
        return this;
    }
}
