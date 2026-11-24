import java.util.function.Function;

/**
 * Two method references of different targets without captures, invoked
 * interleaved (A, B, A) with one receiver variable as first actual
 * argument, so that the variable has lambda invocations of two targets.
 * Each callee stores the next object into the field the receiver is read
 * from, so new objects reach the receiver variable after the invocations
 * are known.
 */
public class LambdaSharedTargets {

    static Shape holder;

    public static void main(String[] args) {
        holder = new Circle();
        Function<Shape, Object> f = Shape::name;
        Function<Object, String> g = Object::toString;
        Shape x = holder;
        f.apply(x);
        g.apply(x);
        f.apply(x);
        g.apply(x);
    }
}

interface Shape {
    Object name();
}

class Circle implements Shape {

    public Object name() {
        LambdaSharedTargets.holder = new Square();
        return this;
    }

    public String toString() {
        LambdaSharedTargets.holder = new Triangle();
        return "circle";
    }
}

class Square implements Shape {

    public Object name() {
        LambdaSharedTargets.holder = new Triangle();
        return this;
    }

    public String toString() {
        return "square";
    }
}

class Triangle implements Shape {

    public Object name() {
        return this;
    }

    public String toString() {
        return "triangle";
    }
}
