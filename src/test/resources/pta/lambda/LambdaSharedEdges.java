import java.util.function.Function;

/**
 * The StateDefinition shape: capturing Function lambdas with static bodies,
 * made from several sources (one lambda object per creating receiver), all
 * called at one call site in one context, so one CS callee; and two
 * non-capturing method references of one static target at that call site.
 */
public class LambdaSharedEdges {

    public static void main(String[] args) {
        Def d1 = new Def();
        Def d2 = new Def();
        Def d3 = new Def();
        Function<Object, Object> f1 = d1.make(new First());
        Function<Object, Object> f2 = d2.make(new Second());
        Function<Object, Object> f3 = d3.make(new Third());
        Object r1 = apply(f1, new Arg());
        Object r2 = apply(f2, new Arg());
        Object r3 = apply(f3, new Arg());
        Function<Object, Object> g = Def::id;
        Function<Object, Object> h = Def::id;
        Object r4 = apply(g, new Arg());
        Object r5 = apply(h, new Arg());
    }

    static Object apply(Function<Object, Object> f, Object a) {
        return f.apply(a);
    }

    static class Def {

        Function<Object, Object> make(Object v) {
            return x -> combine(v, x);
        }

        static Object combine(Object v, Object x) {
            return v;
        }

        static Object id(Object x) {
            return x;
        }
    }

    static class First {
    }

    static class Second {
    }

    static class Third {
    }

    static class Arg {
    }
}
