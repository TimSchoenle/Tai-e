class TypeFilterModel {
    public static void main(String[] args) {
        // each factory object is a heap context of the objects it makes
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
        new Factory().make();
    }
}

class Factory {
    Object[] make() {
        Object[] all = new Object[16];
        all[0] = new A();
        all[1] = new B();
        all[2] = new C();
        all[3] = new D();
        all[4] = new E();
        all[5] = new F();
        all[6] = new G();
        all[7] = new A();
        all[8] = new B();
        all[9] = new E();
        all[10] = new A[1];
        all[11] = new B[1];
        all[12] = new I[1];
        all[13] = new Object();
        all[14] = new G();
        all[15] = new C();
        return all;
    }
}

interface I {
}

interface J extends I {
}

class A {
}

class B extends A implements I {
}

class C extends B {
}

class D extends A implements J {
}

class E implements J {
}

class F extends E {
}

class G {
}
