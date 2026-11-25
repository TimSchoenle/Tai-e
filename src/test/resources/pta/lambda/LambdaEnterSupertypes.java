import java.util.function.Function;

/**
 * Three method references without captures, invoked interleaved on one
 * receiver variable of type Object, each target declared above the classes
 * of the receivers that dispatch it: SupBase::step is inherited over two and
 * three superclasses, SupRoot::name is a default method of a superinterface
 * of the interface the receiver classes implement, and Object::toString
 * dispatches on an array receiver as on every class. Each callee in the
 * application stores the next object into the field the receiver is read
 * from, so new receiver types reach the variable after the invocations are
 * known.
 */
public class LambdaEnterSupertypes {

    static Object holder;

    @SuppressWarnings("unchecked")
    public static void main(String[] args) {
        holder = new SupLeaf();
        Function<Object, Object> inherited = (Function<Object, Object>) (Function<?, ?>)
                (Function<SupBase, Object>) SupBase::step;
        Function<Object, Object> deep = (Function<Object, Object>) (Function<?, ?>)
                (Function<SupRoot, Object>) SupRoot::name;
        Function<Object, Object> shown = (Function<Object, Object>) (Function<?, ?>)
                (Function<Object, String>) Object::toString;
        Object x = holder;
        inherited.apply(x);
        deep.apply(x);
        shown.apply(x);
        inherited.apply(x);
        deep.apply(x);
        shown.apply(x);
    }
}

class SupBase {

    public Object step() {
        LambdaEnterSupertypes.holder = new SupImpl();
        return this;
    }
}

class SupMiddle extends SupBase {
}

class SupLeaf extends SupMiddle {
}

interface SupRoot {

    default Object name() {
        LambdaEnterSupertypes.holder = new long[0];
        return this;
    }
}

interface SupChild extends SupRoot {
}

class SupImpl implements SupChild {

    @Override
    public String toString() {
        LambdaEnterSupertypes.holder = new SupTwig();
        return "impl";
    }
}

class SupTwig extends SupLeaf implements SupChild {
}
