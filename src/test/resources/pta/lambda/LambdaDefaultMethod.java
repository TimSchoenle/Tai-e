/**
 * A lambda without captured variables, created under two receiver contexts
 * of {@code DefaultMethodMaker}, is the receiver of a call to a default
 * method of its functional interface. A context selector of limit 2 puts
 * the receiver's heap context into the context of that default method.
 */
public class LambdaDefaultMethod {

    public static void main(String[] args) {
        DefaultMethodMaker m1 = new DefaultMethodMaker();
        DefaultMethodMaker m2 = new DefaultMethodMaker();
        m1.make().describe();
        m2.make().describe();
    }
}

interface Described {

    Object value();

    default Object describe() {
        return this;
    }
}

class DefaultMethodMaker {

    Described make() {
        return DefaultMethodMaker::fresh;
    }

    static Object fresh() {
        return new Object();
    }
}
