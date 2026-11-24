public class ExceptionSharedCallSite {

    interface Task {
        void run();
    }

    static class A implements Task {
        public void run() {
            Util.fail();
        }
    }

    static class B implements Task {
        public void run() {
            Util.fail();
        }
    }

    static class C implements Task {
        public void run() {
            Util.fail();
        }
    }

    static class Util {
        static void fail() {
            throw new IllegalStateException();
        }
    }

    /**
     * Eight call sites that each call three methods throwing the same
     * (merged) exception object, so the waves of the second and third
     * callee find the call sites already throwing it.
     */
    public static void main(String[] args) {
        Task[] tasks = {new A(), new B(), new C()};
        Task t = tasks[args.length];
        try {
            t.run();
            t.run();
            t.run();
            t.run();
            t.run();
            t.run();
            t.run();
            t.run();
        } catch (IllegalStateException e) {
        }
        callAgain(t);
    }

    static void callAgain(Task t) {
        try {
            t.run();
            t.run();
        } catch (RuntimeException e) {
        }
    }
}
