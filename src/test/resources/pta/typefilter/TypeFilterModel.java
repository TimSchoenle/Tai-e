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
        // more object types than one word of a type memo holds
        new Shapes().make();
    }
}

class Shapes {
    Object[] make() {
        Object[] all = new Object[60];
        all[0] = new A[1][];
        all[1] = new A[1][][];
        all[2] = new A[1][][][];
        all[3] = new A[1][][][][];
        all[4] = new A[1][][][][][];
        all[5] = new A[1][][][][][][];
        all[6] = new B[1][];
        all[7] = new B[1][][];
        all[8] = new B[1][][][];
        all[9] = new B[1][][][][];
        all[10] = new B[1][][][][][];
        all[11] = new B[1][][][][][][];
        all[12] = new C[1][];
        all[13] = new C[1][][];
        all[14] = new C[1][][][];
        all[15] = new C[1][][][][];
        all[16] = new C[1][][][][][];
        all[17] = new C[1][][][][][][];
        all[18] = new D[1][];
        all[19] = new D[1][][];
        all[20] = new D[1][][][];
        all[21] = new D[1][][][][];
        all[22] = new D[1][][][][][];
        all[23] = new D[1][][][][][][];
        all[24] = new E[1][];
        all[25] = new E[1][][];
        all[26] = new E[1][][][];
        all[27] = new E[1][][][][];
        all[28] = new E[1][][][][][];
        all[29] = new E[1][][][][][][];
        all[30] = new F[1][];
        all[31] = new F[1][][];
        all[32] = new F[1][][][];
        all[33] = new F[1][][][][];
        all[34] = new F[1][][][][][];
        all[35] = new F[1][][][][][][];
        all[36] = new G[1][];
        all[37] = new G[1][][];
        all[38] = new G[1][][][];
        all[39] = new G[1][][][][];
        all[40] = new G[1][][][][][];
        all[41] = new G[1][][][][][][];
        all[42] = new I[1][];
        all[43] = new I[1][][];
        all[44] = new I[1][][][];
        all[45] = new I[1][][][][];
        all[46] = new I[1][][][][][];
        all[47] = new I[1][][][][][][];
        all[48] = new J[1][];
        all[49] = new J[1][][];
        all[50] = new J[1][][][];
        all[51] = new J[1][][][][];
        all[52] = new J[1][][][][][];
        all[53] = new J[1][][][][][][];
        all[54] = new Object[1][];
        all[55] = new Object[1][][];
        all[56] = new Object[1][][][];
        all[57] = new Object[1][][][][];
        all[58] = new Object[1][][][][][];
        all[59] = new Object[1][][][][][][];
        return all;
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
