class Census {
    public static void main(String[] args) {
        Object x = new Object();
        Object y = new Object();
        Object t = x;
        for (int i = 0; i < args.length; i++) {
            t = x;
            x = y;
            y = t;
        }
        Object z = (String) t;
        use(x, y, z);
    }

    static void use(Object a, Object b, Object c) {
    }
}
