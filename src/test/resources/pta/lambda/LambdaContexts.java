import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Method references without captured variables (instance {@code Item::name},
 * static {@code Item::id}, constructor {@code Item::new}) and a capturing
 * lambda, each created under three receiver contexts of {@code Maker} and
 * called at one site.
 */
public class LambdaContexts {

    public static void main(String[] args) {
        Maker m1 = new Maker();
        Maker m2 = new Maker();
        Maker m3 = new Maker();
        apply(m1.make(), new Item());
        apply(m2.make(), new Item());
        apply(m3.make(), new Item());
        capture(m1.prefix(new Tag()), new Item());
        capture(m2.prefix(new Tag()), new Item());
        capture(m3.prefix(new Tag()), new Item());
        applyStatic(m1.statics(), new Item());
        applyStatic(m2.statics(), new Item());
        applyStatic(m3.statics(), new Item());
        create(m1.creates());
        create(m2.creates());
        create(m3.creates());
    }

    static Object apply(Function<Item, Object> f, Item item) {
        return f.apply(item);
    }

    static Object capture(Function<Item, Object> f, Item item) {
        return f.apply(item);
    }

    static Object applyStatic(Function<Item, Object> f, Item item) {
        return f.apply(item);
    }

    static Item create(Supplier<Item> s) {
        Item created = s.get();
        return created;
    }
}

class Maker {

    Function<Item, Object> make() {
        return Item::name;
    }

    Function<Item, Object> prefix(Tag tag) {
        return item -> Item.join(tag, item);
    }

    Function<Item, Object> statics() {
        return Item::id;
    }

    Supplier<Item> creates() {
        return Item::new;
    }
}

class Item {

    Object name() {
        return this;
    }

    static Object join(Tag tag, Item item) {
        return tag;
    }

    static Object id(Item item) {
        return item;
    }
}

class Tag {
}
