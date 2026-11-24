import java.util.function.Supplier;

/**
 * One capturing method reference invoked at two call sites, so that its
 * captured receiver variable has two lambda invocations of one target.
 * Each callee stores the next object into the field the receiver is read
 * from, so new objects reach the receiver variable after both invocations
 * are known.
 */
public class LambdaSharedReceiver {

    static Named holder;

    public static void main(String[] args) {
        holder = new First();
        Named n = holder;
        Supplier<Object> s = n::name;
        get1(s);
        get2(s);
        Named m = holder;
        Supplier<Object> t = m::name;
        get1(t);
    }

    static Object get1(Supplier<Object> s) {
        return s.get();
    }

    static Object get2(Supplier<Object> s) {
        return s.get();
    }
}

interface Named {
    Object name();
}

class First implements Named {

    public Object name() {
        LambdaSharedReceiver.holder = new Second();
        return this;
    }
}

class Second implements Named {

    public Object name() {
        LambdaSharedReceiver.holder = new Third();
        return this;
    }
}

class Third implements Named {

    public Object name() {
        LambdaSharedReceiver.holder = new Fourth();
        return this;
    }
}

class Fourth implements Named {

    public Object name() {
        return this;
    }
}
