class FanOut {
    public static void main(String[] args) {
        Object o = new B();
        A a1 = (A) o;
        A a2 = (A) o;
        A a3 = (A) o;
        A a4 = (A) o;
        A a5 = (A) o;
        A a6 = (A) o;
        B b1 = (B) o;
        B b2 = (B) o;
        B b3 = (B) o;
        B b4 = (B) o;
        use(a1, a2, a3, a4, a5, a6);
        use(b1, b2, b3, b4, b1, b2);
        allocate();
    }

    static void use(A x1, A x2, A x3, A x4, A x5, A x6) {
    }

    // more allocation sites of A than a small points-to set holds
    static void allocate() {
        A m1 = new A();
        A m2 = new A();
        A m3 = new A();
        A m4 = new A();
        A m5 = new A();
        A m6 = new A();
        A m7 = new A();
        A m8 = new A();
        A m9 = new A();
        A m10 = new A();
        A m11 = new A();
        A m12 = new A();
    }
}

class A {
}

class B extends A {
}
