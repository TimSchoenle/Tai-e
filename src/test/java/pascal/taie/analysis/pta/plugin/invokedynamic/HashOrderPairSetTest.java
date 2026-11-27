/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.plugin.invokedynamic;

import org.junit.jupiter.api.Test;
import pascal.taie.util.collection.HybridHashSet;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * {@link HashOrderPairSet} against a {@link HybridHashSet} of pair objects
 * with the same hash codes, fed the same adds: every add returns the same,
 * and after every add both have the same size and iterate in the same order.
 */
class HashOrderPairSetTest {

    @Test
    void randomHashesWithDuplicatesKeepTheHybridSetOrder() {
        Random random = new Random(20261125L);
        for (int round = 0; round < 40; ++round) {
            int distinct = 1 + random.nextInt(round < 20 ? 40 : 1500);
            Key[] firsts = keys(random, 1 + distinct / 3);
            Key[] seconds = keys(random, 4);
            Differential d = new Differential();
            int adds = distinct * 2;
            for (int i = 0; i < adds; ++i) {
                d.add(firsts[random.nextInt(firsts.length)],
                        seconds[random.nextInt(seconds.length)]);
            }
            d.checkOrder();
        }
    }

    /**
     * A duplicate added at the small set's size already moves the elements
     * into hash order, as {@link HybridHashSet} moves them before it looks
     * for the element.
     */
    @Test
    void duplicateAtTheSmallSizeStartsHashOrder() {
        int small = new HybridHashSet<>().getThreshold();
        Differential d = new Differential();
        Key first = new Key(0, 0);
        List<Key> seconds = new ArrayList<>();
        for (int i = 0; i < small; ++i) {
            // descending buckets: hash order is the reverse of insertion order
            Key second = new Key(i + 1, small - i);
            seconds.add(second);
            d.add(first, second);
        }
        List<Object> insertionOrder = d.order();
        d.add(first, seconds.get(0));
        assertNotEquals(insertionOrder, d.order(),
                "the duplicate did not move the set into hash order");
    }

    /**
     * Distinct hashes that share their low bits fill one bucket: the table
     * resizes instead of making a tree bin while it is small, and from
     * {@code MIN_TREEIFY_CAPACITY} the set replays into a real set, whose
     * tree bin keeps the order of the reference.
     */
    @Test
    void crowdedBucketResizesThenReplays() {
        Differential d = new Differential();
        Key first = new Key(0, 0);
        for (int i = 1; i <= 10; ++i) {
            // spread hash with zero low bits: bucket 0 of every table up to 256
            d.add(first, new Key(i, i << 24));
        }
        assertNull(d.set.replayForTest(),
                "ten elements in one bucket of a table below 64 resize it");
        for (int i = 11; i <= 40; ++i) {
            d.add(first, new Key(i, i << 24));
        }
        assertNotNull(d.set.replayForTest(), "the crowded bucket did not replay");
        for (int i = 41; i <= 300; ++i) {
            d.add(first, new Key(i, i * 0x9E3779B9));
        }
        d.checkOrder();
    }

    /**
     * Equal hashes of distinct pairs share a bucket in insertion order.
     */
    @Test
    void equalHashesKeepInsertionOrderInTheirBucket() {
        Differential d = new Differential();
        Key first = new Key(0, 0);
        for (int i = 1; i <= 100; ++i) {
            d.add(first, new Key(i, i % 20 == 0 ? 20 : i * 0x61C88647));
        }
        d.checkOrder();
    }

    private static Key[] keys(Random random, int count) {
        Key[] keys = new Key[count];
        for (int i = 0; i < count; ++i) {
            keys[i] = new Key(i, random.nextInt());
        }
        return keys;
    }

    /**
     * A component of a pair, equal by id, with a given hash code.
     */
    private record Key(int id, int hash) {

        @Override
        public boolean equals(Object o) {
            return o instanceof Key that && id == that.id;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /**
     * The reference pair object, hashed as {@link TestSet#hash}.
     */
    private record Ref(Key a, Key b) {

        @Override
        public int hashCode() {
            return 31 * a.hashCode() + b.hashCode();
        }
    }

    private static final class TestSet extends HashOrderPairSet<Key, Key> {

        @Override
        protected int hash(Key a, Key b) {
            return 31 * a.hashCode() + b.hashCode();
        }

        Object replayForTest() {
            try {
                var field = HashOrderPairSet.class.getDeclaredField("replay");
                field.setAccessible(true);
                return field.get(this);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }

    /**
     * Applies each add to both sets and compares them.
     */
    private static final class Differential {

        private final TestSet set = new TestSet();

        private final Set<Ref> reference = new HybridHashSet<>();

        private int adds;

        /**
         * Looks the pair up in both sets first (a lookup must not change the
         * order the later comparison reads), then adds to both sets and
         * compares the results and sizes, and the orders after every add
         * while the sets are small and after every 31st add later.
         */
        void add(Key a, Key b) {
            assertEquals(reference.contains(new Ref(a, b)), set.contains(a, b),
                    "contains of " + a + ", " + b);
            boolean expected = reference.add(new Ref(a, b));
            assertEquals(expected, set.add(a, b), "add of " + a + ", " + b);
            assertEquals(reference.size(), set.size());
            if (reference.size() < 128 || ++adds % 31 == 0) {
                checkOrder();
            }
        }

        void checkOrder() {
            List<Object> expectedOrder = new ArrayList<>();
            reference.forEach(ref -> {
                expectedOrder.add(ref.a());
                expectedOrder.add(ref.b());
            });
            assertEquals(expectedOrder, order(), "order after " + reference.size());
        }

        List<Object> order() {
            List<Object> order = new ArrayList<>();
            set.forEach((a, b) -> {
                order.add(a);
                order.add(b);
            });
            return order;
        }
    }
}
