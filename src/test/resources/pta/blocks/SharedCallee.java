/**
 * The fixture of option call-batching: the receiver of s.area() and
 * s.self() in call() comes from one static field that holds three Round
 * and two Box objects, so one call site has several receiver objects per
 * callee. Under object sensitivity each receiver object selects its own
 * callee context; under call-site sensitivity they share one.
 */
class SharedCallee {

    static Figure shared;

    public static void main(String[] args) {
        shared = new Round();
        shared = new Round();
        shared = new Round();
        shared = new Box();
        shared = new Box();
        call();
        call();
    }

    static void call() {
        Figure s = shared;
        s.area();
        s.self();
    }
}

abstract class Figure {

    abstract Object area();

    Figure self() {
        return this;
    }
}

class Round extends Figure {
    Object area() {
        return new Object();
    }
}

class Box extends Figure {
    Object area() {
        return new Object();
    }
}
