import java.util.function.Function;

/**
 * The fixture of call-hubs with lambda-shared-edges: m.make(x) in run()
 * reaches three Maker nodes at once (a hub), and each make returns a lambda
 * whose apply call site f.apply(x) then has several sources per callee:
 * the method reference Holder::id from M1 and M2 (non-capturing, one
 * static target) and the bound reference h::inst from M1 and M3
 * (capturing, one instance target). Without shared edges each source
 * stores its own lambda edge; with them one edge per call site, callee and
 * passing shape.
 */
class HubLambda {

    static Maker shared;

    public static void main(String[] args) {
        shared = new M1();
        shared = new M2();
        shared = new M3();
        pick = new FA();
        pick = new FB();
        pick = Holder::id;
        run(new Object());
        run(new Object());
    }

    static Function<Object, Object> pick;

    static Object run(Object x) {
        Maker m = shared;
        Function<Object, Object> f = m.make(x);
        Function<Object, Object> g = m.bound(x);
        Object a = f.apply(x);
        Object b = g.apply(a);
        // one site with a hub (FA, FB) and a stored lambda edge (Holder::id)
        Function<Object, Object> p = pick;
        Object c = p.apply(b);
        // the marker methods get hub members (m.marker()) and lambda edges
        // (the unbound reference Maker::marker) as callees
        Function<Maker, Object> r = Maker::marker;
        Object d = r.apply(m);
        Object e = m.marker();
        return c != null ? d : e;
    }
}

class FA implements Function<Object, Object> {
    public Object apply(Object o) {
        return o;
    }
}

class FB implements Function<Object, Object> {
    public Object apply(Object o) {
        return new Object();
    }
}

interface Maker {
    Object marker();

    Function<Object, Object> make(Object x);

    Function<Object, Object> bound(Object x);
}

class Holder {
    Object kept;

    static Object id(Object o) {
        return o;
    }

    Object inst(Object o) {
        kept = o;
        return kept;
    }
}

class M1 implements Maker {
    public Object marker() {
        return this;
    }

    public Function<Object, Object> make(Object x) {
        return Holder::id;
    }

    public Function<Object, Object> bound(Object x) {
        Holder h = new Holder();
        return h::inst;
    }
}

class M2 implements Maker {
    public Object marker() {
        return this;
    }

    public Function<Object, Object> make(Object x) {
        return Holder::id;
    }

    public Function<Object, Object> bound(Object x) {
        return y -> x;
    }
}

class M3 implements Maker {
    public Object marker() {
        return this;
    }

    public Function<Object, Object> make(Object x) {
        return y -> new Object();
    }

    public Function<Object, Object> bound(Object x) {
        Holder h = new Holder();
        return h::inst;
    }
}
