import java.util.function.Supplier;

/**
 * A lambda without captured variables, created under two receiver contexts
 * of {@code FieldBaseMaker}, reaches the base of a field store and a field
 * load. Java code cannot access a field of a lambda object, so the test
 * plugin {@code LambdaFieldBasePlugin} models {@code FieldBaseSink.store}
 * and {@code FieldBaseSink.load} as an unfiltered store and load of
 * {@code FieldBaseSink.cell} on every lambda object their {@code base}
 * points to.
 */
public class LambdaFieldBase {

    public static void main(String[] args) {
        FieldBaseMaker m1 = new FieldBaseMaker();
        FieldBaseMaker m2 = new FieldBaseMaker();
        m1.roundTrip(new FieldBaseValue());
        m2.roundTrip(new FieldBaseValue());
    }
}

class FieldBaseMaker {

    Object roundTrip(Object value) {
        Supplier<Object> lambda = FieldBaseMaker::fresh;
        FieldBaseSink.store(lambda, value);
        return FieldBaseSink.load(lambda);
    }

    static Object fresh() {
        return new FieldBaseValue();
    }
}

class FieldBaseSink {

    Object cell;

    static void store(Object base, Object value) {
    }

    static Object load(Object base) {
        Object loaded = null;
        return loaded;
    }
}

class FieldBaseValue {
}
