import java.util.function.Supplier;

/**
 * The call block probe's fixture: the receiver of shape.area() in drawAll
 * comes from one static field, so the two contexts of drawAll get equal
 * receiver diffs; plus a bound, an unbound, a static and a constructor
 * method reference.
 */
class Blocks {

    static Shape shared;

    public static void main(String[] args) {
        shared = new Circle();
        shared = new Square();
        drawAll();
        drawAll();
        Runnable run = Blocks::helper;
        run.run();
        Shape s = shared;
        Supplier<Object> bound = s::area;
        bound.get();
        Area unbound = Shape::area;
        unbound.of(s);
        Supplier<Shape> make = Circle::new;
        make.get();
    }

    static void drawAll() {
        Shape shape = shared;
        shape.area();
    }

    static void helper() {
    }
}

interface Area {
    Object of(Shape s);
}

abstract class Shape {
    abstract Object area();
}

class Circle extends Shape {
    Object area() {
        return new Object();
    }
}

class Square extends Shape {
    Object area() {
        return new Object();
    }
}
