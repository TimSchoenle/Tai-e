import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Lambdas with and without captured variables, created in instance methods
 * called on two receivers (so under two contexts of the creating method),
 * returned, nested, invoked through method references on lambda receivers,
 * and method references to instance methods and constructors. No lambda
 * object is the base of a field or an array access.
 */
public class LambdaMix {

    public static void main(String[] args) {
        MixBox a = new MixBox(new MixItem());
        MixBox b = new MixBox(new MixItem());
        Supplier<Object> sa = a.supplier();
        Supplier<Object> sb = b.supplier();
        sa.get();
        sb.get();
        Function<Object, Object> fa = a.mapper();
        Function<Object, Object> fb = b.mapper();
        fa.apply(new MixItem());
        fb.apply("text");
        Function<Supplier<Object>, Object> run = Supplier::get;
        run.apply(sa);
        run.apply(a.self());
        run.apply(b.self());
        a.nested().get().get();
        b.nested().get().get();
        BiFunction<MixBox, Object, Object> put = MixBox::put;
        put.apply(a, new MixItem());
        put.apply(b, sb);
        Supplier<MixBox> make = () -> new MixBox(new MixItem());
        make.get().supplier().get();
        Function<Object, MixBox> ctor = MixBox::new;
        ctor.apply(fa).mapper().apply(a);
    }
}

class MixItem {
}

class MixBox {

    Object content;

    MixBox(Object content) {
        this.content = content;
    }

    Supplier<Object> supplier() {
        return () -> new MixItem();
    }

    Function<Object, Object> mapper() {
        return x -> wrap(x);
    }

    Supplier<Supplier<Object>> nested() {
        return () -> () -> content;
    }

    Supplier<Object> self() {
        return this::current;
    }

    Object wrap(Object x) {
        return new MixBox(x);
    }

    Object put(Object x) {
        content = x;
        return content;
    }

    Object current() {
        return content;
    }
}
