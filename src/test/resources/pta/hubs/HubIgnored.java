/**
 * The ignored-target fixture of option call-hubs (tests run with
 * only-app:true, so library methods are ignored): o.equals(x) and
 * o.toString() in call() reach Object's library methods and two app
 * overrides at once, so each hub holds an ignored target beside analyzed
 * ones; q.toString() reaches library methods only, so its hub holds no
 * analyzed target. The ignored targets get neither arguments nor returns.
 */
class HubIgnored {

    static Object shared;

    static Object lib;

    public static void main(String[] args) {
        shared = new Object();
        shared = new Named();
        shared = new Other();
        lib = new Object();
        lib = new StringBuilder();
        call(new Object());
        call(new Named());
    }

    static Object call(Object x) {
        Object o = shared;
        boolean same = o.equals(x);
        String s = o.toString();
        Object q = lib;
        String t = q.toString();
        return same ? s : t;
    }
}

class Named {
    Object seen;

    public boolean equals(Object other) {
        seen = other;
        return false;
    }

    public String toString() {
        return "named";
    }
}

class Other {
    Object seen;

    public boolean equals(Object other) {
        seen = other;
        return true;
    }

    public String toString() {
        return "other";
    }
}
