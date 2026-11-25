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

package pascal.taie.analysis.pta.core.cs.element;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Checks {@link ContextElementMap} against the map it replaces,
 * {@link Maps#newTwoKeyMap()}: same lookups, same sizes and the same
 * iteration orders under the same sequence of insertions, including keys and
 * contexts whose hash codes collide so often that {@link java.util.HashMap}
 * turns their bins into trees.
 */
class ContextElementMapTest {

    /**
     * Key with a chosen hash code and identity equality, like a {@code Var}
     * whose identity hash codes collide.
     */
    private static final class Key {

        private final int hash;

        private Key(int hash) {
            this.hash = hash;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /**
     * Context with a chosen hash code and identity equality.
     */
    private static final class TestContext implements Context {

        private final int hash;

        private TestContext(int hash) {
            this.hash = hash;
        }

        @Override
        public int getLength() {
            return 0;
        }

        @Override
        public Object getElementAt(int i) {
            throw new IndexOutOfBoundsException(i);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    private record Element(Context context) implements CSElement {

        @Override
        public Context getContext() {
            return context;
        }
    }

    /**
     * Both maps under test, filled the way {@link MapBasedCSManager} fills
     * them: the reference by {@code computeIfAbsent}, the new map by
     * {@code get} and, on a miss, {@code add}.
     */
    private static final class Pair {

        private final TwoKeyMap<Key, Context, Element> reference = Maps.newTwoKeyMap();

        private final ContextElementMap<Key, Element> map = new ContextElementMap<>();

        private final List<Key> keys = new ArrayList<>();

        /**
         * Looks {@code key} up in {@code context} in both maps and, if that
         * added an element, compares the key orders right away: a resize of
         * the outer map at another time shows only until the next new key.
         */
        void lookUp(Key key, Context context) {
            Element[] created = new Element[1];
            Element expected = reference.computeIfAbsent(key, context, (k, c) -> {
                created[0] = new Element(c);
                return created[0];
            });
            Element actual = map.get(key, context);
            if (created[0] != null) {
                assertNull(actual, "present before the reference created it");
                map.add(key, created[0]);
                actual = map.get(key, context);
                if (!keys.contains(key)) {
                    keys.add(key);
                }
                assertSameSequence(new ArrayList<>(reference.keySet()),
                        new ArrayList<>(map.keySet()));
            }
            assertSame(expected, actual);
        }

        void assertSameOrders() {
            assertEquals(reference.size(), map.values().size());
            assertSameSequence(new ArrayList<>(reference.values()),
                    new ArrayList<>(map.values()));
            assertSameSequence(new ArrayList<>(reference.keySet()),
                    new ArrayList<>(map.keySet()));
            for (Key key : keys) {
                assertSameSequence(new ArrayList<>(reference.get(key).values()),
                        new ArrayList<>(map.valuesOf(key)));
            }
        }
    }

    private static void assertSameSequence(List<?> expected, List<?> actual) {
        assertEquals(expected.size(), actual.size());
        for (int i = 0; i < expected.size(); ++i) {
            assertSame(expected.get(i), actual.get(i), "position " + i);
        }
    }

    @ParameterizedTest
    @ValueSource(longs = {1L, 2L, 3L, 4L, 5L})
    void randomInsertionsKeepEveryOrder(long seed) {
        Random random = new Random(seed);
        List<Key> keys = new ArrayList<>();
        for (int i = 0; i < 400; ++i) {
            keys.add(new Key(random.nextInt()));
        }
        int collidingKeyHash = random.nextInt();
        for (int i = 0; i < 12; ++i) {
            keys.add(new Key(collidingKeyHash));
        }
        List<Context> contexts = new ArrayList<>();
        for (int i = 0; i < 60; ++i) {
            contexts.add(new TestContext(random.nextInt()));
        }
        int collidingContextHash = random.nextInt();
        for (int i = 0; i < 12; ++i) {
            contexts.add(new TestContext(collidingContextHash));
        }
        Pair pair = new Pair();
        for (int step = 0; step < 20_000; ++step) {
            Key key = keys.get(random.nextInt(keys.size()));
            // a skew so that keys reach one, a few and many contexts
            int width = 1 + (key.hashCode() & 0xff) % contexts.size();
            Context context = contexts.get(random.nextInt(width));
            pair.lookUp(key, context);
            if (step % 2_000 == 0) {
                pair.assertSameOrders();
            }
        }
        pair.assertSameOrders();
    }

    @Test
    void aNewContextOfAPresentKeyResizesTheOuterMapAsBefore() {
        Pair pair = new Pair();
        List<Key> keys = new ArrayList<>();
        Context first = new TestContext(1);
        // 13 keys pass the threshold 12 of the default outer table of 16;
        // the odd ones move to other buckets when the table doubles
        for (int i = 0; i < 13; ++i) {
            Key key = new Key(i + (i % 2 == 0 ? 0 : 16));
            keys.add(key);
            pair.lookUp(key, first);
        }
        pair.lookUp(keys.get(0), new TestContext(2));
        pair.assertSameOrders();
    }

    @Test
    void everyShapeOfAKeyKeepsInsertionAndHashOrder() {
        Pair pair = new Pair();
        Key one = new Key(1);
        Key few = new Key(2);
        Key threshold = new Key(3);
        Key many = new Key(4);
        Key treeified = new Key(5);
        List<Context> contexts = new ArrayList<>();
        for (int i = 0; i < 40; ++i) {
            // the last 10 contexts share one hash code
            contexts.add(new TestContext(i < 30 ? 1000 - i * 31 : 77));
        }
        pair.lookUp(one, contexts.get(0));
        for (int i = 0; i < 3; ++i) {
            pair.lookUp(few, contexts.get(i));
        }
        for (int i = 0; i < ContextElementMap.SMALL_SIZE; ++i) {
            pair.lookUp(threshold, contexts.get(i));
        }
        for (int i = ContextElementMap.SMALL_SIZE + 1; i >= 0; --i) {
            pair.lookUp(many, contexts.get(i));
        }
        for (Context context : contexts) {
            pair.lookUp(treeified, context);
            pair.lookUp(treeified, context);
        }
        pair.assertSameOrders();
        assertNull(pair.map.get(one, contexts.get(1)));
        assertNull(pair.map.get(new Key(1), contexts.get(0)));
        assertEquals(0, pair.map.valuesOf(new Key(9)).size());
    }

    @Test
    void addRefusesAnElementWithoutContext() {
        ContextElementMap<Key, Element> map = new ContextElementMap<>();
        assertThrows(NullPointerException.class,
                () -> map.add(new Key(1), new Element(null)));
    }
}
