/**
 * Option trivial-getters: calls to trivial getters (instance field, static
 * field, null; in an instance and a static method), on one receiver and on
 * merged receivers, through super, overridden by a trivial and by a
 * non-trivial getter, next to getters that are not trivial (a cast, a
 * parameter, a primitive result). The results drive further calls, so a
 * lost object would lose a call edge.
 */
public class Getters {

    public static void main(String[] args) {
        Box b1 = new Box();
        b1.v = new GtA();
        Box b2 = new Box();
        b2.v = new GtB();
        // one receiver each
        ((Runnable) b1.get()).run();
        ((Runnable) b2.get()).run();
        // merged receivers
        Box m = args.length > 0 ? b1 : b2;
        Object merged = m.get();
        ((Runnable) merged).run();
        // a receiver that arrives through a factory, with a later store
        Factory f1 = new Factory();
        Box made = f1.make(new GtC());
        ((Runnable) made.get()).run();
        Factory f2 = new Factory();
        Box made2 = f2.make(new GtA());
        Object fromMade2 = made2.get();
        made2.v = new GtD();
        ((Runnable) fromMade2).run();
        // static field getters, in a static and an instance method
        Holder.cell = new GtB();
        ((Runnable) Holder.sget()).run();
        ((Runnable) b1.viaStatic()).run();
        // null getters
        Object none = b1.nothing();
        Object staticNone = Holder.none();
        // a getter that is not trivial: its cast filters the field
        GtA onlyA = m.getA();
        onlyA.run();
        // not trivial: a parameter, a primitive result
        ((Runnable) b1.pick(b2)).run();
        int size = b1.size();
        // dispatch: a trivial getter, its trivial and its non-trivial override
        Base k = args.length > 1 ? new Base(new GtA())
                : args.length > 2 ? new Sub1(new GtB(), new GtC()) : new Sub2(new GtD());
        ((Runnable) k.val()).run();
        // a getter of a getter result
        Box outer = new Box();
        outer.v = b2;
        ((Runnable) ((Box) outer.get()).get()).run();
        PTAAssert.notEmpty(merged, fromMade2, onlyA);
        PTAAssert.reachable("<GtA: void run()>", "<GtB: void run()>", "<GtC: void run()>",
                "<GtD: void run()>");
    }
}

class Box {
    Object v;

    int n;

    Object get() {
        return v;
    }

    Object viaStatic() {
        return Holder.cell;
    }

    Object nothing() {
        return null;
    }

    GtA getA() {
        return (GtA) v;
    }

    Object pick(Box other) {
        return other.v;
    }

    int size() {
        return n;
    }
}

class Factory {
    Box make(Object v) {
        Box b = new Box();
        b.v = v;
        return b;
    }
}

class Holder {
    static Object cell;

    static Object sget() {
        return cell;
    }

    static Object none() {
        return null;
    }
}

class Base {
    Object field;

    Base(Object field) {
        this.field = field;
    }

    Object val() {
        return field;
    }
}

class Sub1 extends Base {
    Object other;

    Sub1(Object field, Object other) {
        super(field);
        this.other = other;
    }

    @Override
    Object val() {
        return other;
    }
}

class Sub2 extends Base {
    Sub2(Object field) {
        super(field);
    }

    @Override
    Object val() {
        Object fromSuper = super.val();
        return fromSuper;
    }
}

class GtA implements Runnable {
    public void run() {
    }
}

class GtB implements Runnable {
    public void run() {
    }
}

class GtC implements Runnable {
    public void run() {
    }
}

class GtD implements Runnable {
    public void run() {
    }
}
