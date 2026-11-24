public class CatchDispatch {

    public static void main(String[] args) {
        try {
            fail();
        } catch (CatchDispatchBase e) {
            e.describe();
        }
    }

    static void fail() {
        throw new CatchDispatchSub();
    }
}

class CatchDispatchBase extends RuntimeException {

    void describe() {
    }
}

class CatchDispatchSub extends CatchDispatchBase {

    @Override
    void describe() {
    }
}
