/**
 * The fixture of option call-hubs: s.id(x) in call() has the receivers of
 * one static field, two Echo-like classes and one Fresh, so its call site
 * reaches three callee nodes at once (a hub). Under call-site sensitivity
 * each call of call() is a context of that call site with the same callee
 * nodes, so the later contexts join the hub of the first (late joiners),
 * and each passes its own argument: the hub's argument relay grows with
 * every member and its return relay carries the union back to every
 * member. later()'s receiver field gets Twice only through make()'s
 * return, usually after Echo and Fresh, so its site may link a hub of two
 * nodes first and the third node later.
 */
class HubJoin {

    static Shape shared;

    static Shape partial;

    public static void main(String[] args) {
        shared = new Echo();
        shared = new Twice();
        shared = new Fresh();
        Object r1 = call(new Object());
        Object r2 = call(new Object());
        Object r3 = call(new Object());
        partial = new Echo();
        partial = new Fresh();
        later(new Object());
        partial = make();
        later(new Object());
    }

    static Shape make() {
        return new Twice();
    }

    static Object call(Object x) {
        Shape s = shared;
        return s.id(x);
    }

    static Object later(Object x) {
        Shape p = partial;
        return p.id(x);
    }
}

interface Shape {
    Object id(Object x);
}

class Echo implements Shape {
    public Object id(Object x) {
        return x;
    }
}

class Twice implements Shape {
    public Object id(Object x) {
        Object y = x;
        return y;
    }
}

class Fresh implements Shape {
    public Object id(Object x) {
        return new Object();
    }
}
