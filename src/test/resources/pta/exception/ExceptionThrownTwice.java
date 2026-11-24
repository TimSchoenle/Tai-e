public class ExceptionThrownTwice {

    public static void main(String[] args) {
        try {
            thrower(args.length);
        } catch (Error e) {
        }
    }

    /**
     * Two throw statements throw the same object: the second adds nothing
     * to the uncaught set of the method.
     */
    static void thrower(int n) {
        RuntimeException e = new RuntimeException();
        if (n > 0) {
            throw e;
        }
        throw e;
    }
}
