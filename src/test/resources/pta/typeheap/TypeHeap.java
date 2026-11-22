import java.lang.reflect.Array;

class TypeHeap {

    static class Box {
        Object f;
    }

    interface Shape {
        void draw();
    }

    static class Square implements Shape {
        public void draw() {
        }
    }

    static class Circle implements Shape {
        public void draw() {
        }
    }

    public static void main(String[] args) {
        Shape shape = args.length > 0 ? new Square() : new Circle();
        shape.draw();
        Box b1 = new Box();
        Box b2 = new Box();
        Runnable r1 = () -> {
        };
        Runnable r2 = () -> {
        };
        Box[] c1 = new Box[1];
        Box[] c2 = new Box[2];
        int[] a1 = new int[1];
        int[] a2 = new int[2];
        Object[] z1 = new Object[0];
        int[] dims = {2, 3};
        Object grid = Array.newInstance(Box.class, dims);
        b1.f = r1;
        b2.f = r2;
        use(b1, b2, c1, c2, a1, a2, z1, grid);
    }

    static void use(Box b1, Box b2, Box[] c1, Box[] c2, int[] a1, int[] a2,
                    Object[] z1, Object grid) {
    }
}
