import java.util.function.Function;

/**
 * Lambda invocations whose receiver variable is the base variable of the
 * invocation itself (the first actual argument of a method reference
 * without captured arguments is the lambda object's own variable).
 */
public class LambdaSelfReceiver {

    public static void main(String[] args) {
        Function<Object, String> f = Object::toString;
        f.apply(f);
        Function<Object, String> g = Object::toString;
        g = g.apply(g) == null ? g : String::valueOf;
        g.apply(g);
    }
}
