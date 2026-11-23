import java.util.function.Supplier;

/**
 * Application code (on -acp) of the merge-library-objects test: two
 * allocation sites of the same type, the same in a nested class, one in an
 * anonymous class, and calls of the library's sites.
 */
public class LibHeapApp {

    public static void main(String[] args) {
        Object a = first();
        Object b = second();
        Object c = LibHeapLib.first();
        Object d = LibHeapLib.second();
        Object e = LibHeapLib.other();
        Object f = Nested.first();
        Object g = Nested.second();
        Supplier<Object> h = new Supplier<Object>() {
            @Override
            public Object get() {
                return new Item();
            }
        };
        Object i = h.get();
    }

    static Object first() {
        return new Item();
    }

    static Object second() {
        return new Item();
    }

    static class Nested {

        static Object first() {
            return new Item();
        }

        static Object second() {
            return new Item();
        }
    }
}
