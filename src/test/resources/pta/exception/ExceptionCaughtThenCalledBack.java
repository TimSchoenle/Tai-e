public class ExceptionCaughtThenCalledBack {

    public static void main(String[] args) {
        quiet();
    }

    /**
     * Throws and catches everything, so its uncaught set stays empty; the
     * call edge into it from {@link CalledBack#again} appears only after
     * the caught object reaches the catch variable.
     */
    static void quiet() {
        try {
            throw new CalledBack();
        } catch (Throwable t) {
            if (t instanceof CalledBack) {
                ((CalledBack) t).again();
            }
        }
    }
}

class CalledBack extends RuntimeException {

    void again() {
        ExceptionCaughtThenCalledBack.quiet();
    }
}
