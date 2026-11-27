/**
 * A lambda call edge offered again after it is in the call graph: the
 * receiver variable of the call through the method reference gets a second
 * object of the same class only from the target method the first edge
 * reaches, so under call-site contexts the second object resolves to the
 * same context-sensitive callee, whose edge the call graph already holds.
 */
public class LambdaRedundantEdge {

    interface Namer {
        String name(Item item);
    }

    static class Item {
        String name() {
            last = new Item();
            itemBody();
            return "item";
        }
    }

    static Item last;

    public static void main(String[] args) {
        last = new Item();
        Namer namer = Item::name;
        namer.name(last);
    }

    static void itemBody() {
    }
}
