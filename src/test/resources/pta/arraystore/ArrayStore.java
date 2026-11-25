class ArrayStore {

    static Object[] f;

    public static void main(String[] args) {
        // arrays of two element types, interleaved, reach arr in one delta
        f = new A[1];
        f = new B[1];
        f = new A[1];
        f = new B[1];
        f = new A[1];
        f = new B[1];
        f = new A[1];
        f = new B[1];
        Object[] arr = f;
        Object x = new B();
        arr[0] = x;
        arr[1] = x;
        // another stored variable: its own application per filter
        Object z = new A();
        arr[2] = z;
        Object[] read = f;
        Object y = read[0];
    }
}

class A {
}

class B extends A {
}
