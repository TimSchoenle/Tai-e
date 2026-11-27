/**
 * The hub cap fixture of option call-hubs: n.next() in step() first sees
 * A0 and B0, and each pair's next() returns the next pair, which reaches
 * the same call site in one points-to delta through the return relay.
 * So the site links twenty node sets of two, one after the other: the
 * first sixteen become hubs, the later ones stored call edges.
 */
class HubCap {

    static Node cur;

    public static void main(String[] args) {
        cur = new A0();
        cur = new B0();
        step();
    }

    static void step() {
        Node n = cur;
        Node m = n.next();
        cur = m;
    }
}

interface Node {
    Node next();
}

class A0 implements Node {
    public Node next() {
        return new A1();
    }
}

class A1 implements Node {
    public Node next() {
        return new A2();
    }
}

class A2 implements Node {
    public Node next() {
        return new A3();
    }
}

class A3 implements Node {
    public Node next() {
        return new A4();
    }
}

class A4 implements Node {
    public Node next() {
        return new A5();
    }
}

class A5 implements Node {
    public Node next() {
        return new A6();
    }
}

class A6 implements Node {
    public Node next() {
        return new A7();
    }
}

class A7 implements Node {
    public Node next() {
        return new A8();
    }
}

class A8 implements Node {
    public Node next() {
        return new A9();
    }
}

class A9 implements Node {
    public Node next() {
        return new A10();
    }
}

class A10 implements Node {
    public Node next() {
        return new A11();
    }
}

class A11 implements Node {
    public Node next() {
        return new A12();
    }
}

class A12 implements Node {
    public Node next() {
        return new A13();
    }
}

class A13 implements Node {
    public Node next() {
        return new A14();
    }
}

class A14 implements Node {
    public Node next() {
        return new A15();
    }
}

class A15 implements Node {
    public Node next() {
        return new A16();
    }
}

class A16 implements Node {
    public Node next() {
        return new A17();
    }
}

class A17 implements Node {
    public Node next() {
        return new A18();
    }
}

class A18 implements Node {
    public Node next() {
        return new A19();
    }
}

class A19 implements Node {
    public Node next() {
        return null;
    }
}

class B0 implements Node {
    public Node next() {
        return new B1();
    }
}

class B1 implements Node {
    public Node next() {
        return new B2();
    }
}

class B2 implements Node {
    public Node next() {
        return new B3();
    }
}

class B3 implements Node {
    public Node next() {
        return new B4();
    }
}

class B4 implements Node {
    public Node next() {
        return new B5();
    }
}

class B5 implements Node {
    public Node next() {
        return new B6();
    }
}

class B6 implements Node {
    public Node next() {
        return new B7();
    }
}

class B7 implements Node {
    public Node next() {
        return new B8();
    }
}

class B8 implements Node {
    public Node next() {
        return new B9();
    }
}

class B9 implements Node {
    public Node next() {
        return new B10();
    }
}

class B10 implements Node {
    public Node next() {
        return new B11();
    }
}

class B11 implements Node {
    public Node next() {
        return new B12();
    }
}

class B12 implements Node {
    public Node next() {
        return new B13();
    }
}

class B13 implements Node {
    public Node next() {
        return new B14();
    }
}

class B14 implements Node {
    public Node next() {
        return new B15();
    }
}

class B15 implements Node {
    public Node next() {
        return new B16();
    }
}

class B16 implements Node {
    public Node next() {
        return new B17();
    }
}

class B17 implements Node {
    public Node next() {
        return new B18();
    }
}

class B18 implements Node {
    public Node next() {
        return new B19();
    }
}

class B19 implements Node {
    public Node next() {
        return null;
    }
}
