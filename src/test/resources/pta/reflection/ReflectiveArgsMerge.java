import java.lang.reflect.Constructor;
import java.lang.reflect.Method;

/**
 * Reflective calls whose argument arrays merge: one helper call site
 * receives every Method object and every argument array, so each callee
 * parameter must receive the elements of every array that reaches the
 * helper, filtered by the parameter type. A second helper has two
 * Constructor.newInstance call sites sharing one argument variable.
 */
public class ReflectiveArgsMerge {

    public static void main(String[] args) throws Exception {
        Target t = new Target();
        Method one = Target.class.getMethod("one", Object.class);
        Method two = Target.class.getMethod("two", String.class, Target.class);
        Method three = Target.class.getMethod("three", Box.class, int.class, Object[].class);
        Method stat = Target.class.getMethod("stat", Box.class);
        call(one, t, new Object[]{"s1"});
        call(two, t, new Object[]{"s2", new Target()});
        call(three, t, new Object[]{new Box(), new Object[0]});
        call(stat, null, new Object[]{new Box()});
        Constructor<Target> ctor = Target.class.getConstructor(String.class, Box.class);
        make(ctor, new Object[]{"s3", new Box()});
    }

    static Object call(Method m, Object recv, Object[] a) throws Exception {
        return m.invoke(recv, a);
    }

    static Object make(Constructor<Target> c, Object[] a) throws Exception {
        c.newInstance(a);
        return c.newInstance(a);
    }

    static class Box {
    }

    static class Target {

        Object last;

        Target() {
        }

        public Target(String s, Box b) {
            last = s;
            last = b;
        }

        public Object one(Object o) {
            return o;
        }

        public Object two(String s, Target other) {
            last = s;
            return other;
        }

        public Object three(Box b, int i, Object[] rest) {
            last = rest;
            return b;
        }

        public static Object stat(Box b) {
            return b;
        }
    }
}
