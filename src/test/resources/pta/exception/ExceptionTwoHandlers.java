public class ExceptionTwoHandlers {

    public static void main(String[] args) {
        try {
            fail(args.length);
        } catch (IllegalStateException e) {
            e.getMessage();
        } catch (RuntimeException e) {
            e.getMessage();
        }
    }

    static void fail(int n) {
        RuntimeException e;
        switch (n) {
            case 0: e = new TwoHandlers0(); break;
            case 1: e = new TwoHandlers1(); break;
            case 2: e = new TwoHandlers2(); break;
            case 3: e = new TwoHandlers3(); break;
            case 4: e = new TwoHandlers4(); break;
            case 5: e = new TwoHandlers5(); break;
            case 6: e = new TwoHandlers6(); break;
            case 7: e = new TwoHandlers7(); break;
            case 8: e = new TwoHandlers8(); break;
            case 9: e = new TwoHandlers9(); break;
            default: e = new TwoHandlers10(); break;
        }
        throw e;
    }
}

class TwoHandlers0 extends RuntimeException {
}

class TwoHandlers1 extends RuntimeException {
}

class TwoHandlers2 extends RuntimeException {
}

class TwoHandlers3 extends RuntimeException {
}

class TwoHandlers4 extends RuntimeException {
}

class TwoHandlers5 extends RuntimeException {
}

class TwoHandlers6 extends RuntimeException {
}

class TwoHandlers7 extends RuntimeException {
}

class TwoHandlers8 extends RuntimeException {
}

class TwoHandlers9 extends RuntimeException {
}

class TwoHandlers10 extends RuntimeException {
}
