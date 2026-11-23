/**
 * Library code (on -cp) of the merge-library-objects test: two allocation
 * sites of the same type, one of another type.
 */
public class LibHeapLib {

    public static Object first() {
        return new Box();
    }

    public static Object second() {
        return new Box();
    }

    public static Object other() {
        return new LibHeapLib();
    }
}

class Box {
}
