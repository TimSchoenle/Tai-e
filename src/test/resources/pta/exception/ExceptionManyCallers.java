public class ExceptionManyCallers {

    /**
     * Twelve call sites of one throwing method, so its uncaught exceptions
     * go out in one wave over twelve call edges.
     */
    public static void main(String[] args) {
        try {
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
            thrower();
        } catch (RuntimeException e) {
        }
    }

    static void thrower() {
        throw new RuntimeException();
    }
}
