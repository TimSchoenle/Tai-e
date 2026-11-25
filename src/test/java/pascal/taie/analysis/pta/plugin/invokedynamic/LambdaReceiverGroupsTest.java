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
import pascal.taie.util.collection.Maps;

import java.util.ArrayList;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The receiver grouping keeps first-seen order of keys and of objects per
 * key, holds a group of one object without a list, and copies a new list
 * group into an exactly sized list when groups are appended.
 */
class LambdaReceiverGroupsTest {

    private static ReceiverGroups<String, Object> groups(Object... keyThenValues) {
        ReceiverGroups<String, Object> g = new ReceiverGroups<>();
        for (int i = 0; i < keyThenValues.length; i += 2) {
            g.add((String) keyThenValues[i], keyThenValues[i + 1]);
        }
        return g;
    }

    /**
     * @return the same grouping as {@link #groups}, made by
     * {@link ReceiverGroups#group}, packed or open as it chooses. The
     * objects must be distinct.
     */
    private static ReceiverGroups<String, Object> packed(Object... keyThenValues) {
        List<Object> objs = new ArrayList<>();
        Map<Object, String> keyOf = Maps.newMap();
        for (int i = 0; i < keyThenValues.length; i += 2) {
            objs.add(keyThenValues[i + 1]);
            keyOf.put(keyThenValues[i + 1], (String) keyThenValues[i]);
        }
        return ReceiverGroups.group(objs, keyOf::get);
    }

    /**
     * @return the groups as seen through {@link ReceiverGroups#forEachGroup}.
     */
    private static Map<String, List<Object>> contents(ReceiverGroups<String, Object> g) {
        Map<String, List<Object>> m = Maps.newLinkedHashMap();
        g.forEachGroup(new ReceiverGroups.Visitor<String, Object, List<Object>>() {
            @Override
            public List<Object> enter(String key) {
                return m.computeIfAbsent(key, k -> new ArrayList<>());
            }

            @Override
            public void accept(List<Object> list, Object obj) {
                list.add(obj);
            }
        });
        return m;
    }

    @Test
    void addAndAppendKeepFirstSeenOrderOfKeysAndObjects() {
        ReceiverGroups<String, Object> cached = groups("B", 1, "A", 2, "B", 3);
        cached.appendAll(groups("C", 4, "A", 5, "D", 6, "C", 7));
        cached.appendAll(groups("D", 8, "B", 9, "E", 10, "B", 11));
        Map<String, List<Object>> m = contents(cached);
        assertEquals(List.of("B", "A", "C", "D", "E"), new ArrayList<>(m.keySet()));
        assertEquals(List.of(1, 3, 9, 11), m.get("B"));
        assertEquals(List.of(2, 5), m.get("A"));
        assertEquals(List.of(4, 7), m.get("C"));
        assertEquals(List.of(6, 8), m.get("D"));
        assertEquals(List.of(10), m.get("E"));
        assertEquals(5, cached.keyCount());
        assertEquals(11, cached.objectCount());
    }

    @Test
    void singleObjectGroupHoldsNoList() {
        Object a = new Object();
        Object b = new Object();
        ReceiverGroups<String, Object> cached = groups("A", a);
        cached.appendAll(groups("B", b));
        assertSame(a, cached.singleObject("A"));
        assertSame(b, cached.singleObject("B"));
        assertEquals(-1, cached.listCapacity("A"));
        assertEquals(-1, cached.listCapacity("B"));
    }

    @Test
    void secondObjectTurnsTheGroupIntoAList() {
        Object a = new Object();
        Object b = new Object();
        ReceiverGroups<String, Object> g = groups("X", 0, "A", a, "Y", 0);
        g.add("A", b);
        assertNull(g.singleObject("A"));
        assertEquals(2, g.listCapacity("A"));
        assertEquals(List.of(a, b), contents(g).get("A"));
        assertEquals(List.of("X", "A", "Y"), new ArrayList<>(contents(g).keySet()));
    }

    @Test
    void newListGroupIsCopiedExactlySizedAndNotShared() {
        ReceiverGroups<String, Object> cached = groups("Z", 0);
        ReceiverGroups<String, Object> pts = groups("A", 1, "A", 2, "A", 3);
        cached.appendAll(pts);
        assertEquals(3, cached.listCapacity("A"));
        pts.add("A", 4);
        assertEquals(List.of(1, 2, 3), contents(cached).get("A"));
        cached.add("A", 5);
        assertEquals(List.of(1, 2, 3, 4), contents(pts).get("A"));
    }

    /**
     * Growth keeps java.util.ArrayList's capacities for the same sequence of
     * add and addAll calls (an ArrayList of capacity one, as the grouping
     * held before), so a group's footprint is unchanged.
     */
    @Test
    void growthMatchesArrayListCapacities() {
        ReceiverGroups<String, Object> g = groups("A", 1, "A", 2, "A", 3);
        assertEquals(3, g.listCapacity("A"));
        g.add("A", 4);
        assertEquals(4, g.listCapacity("A"));
        g.add("A", 5);
        assertEquals(6, g.listCapacity("A"));
        ReceiverGroups<String, Object> two = groups("B", 1, "B", 2);
        two.appendAll(groups("B", 3, "B", 4));
        assertEquals(4, two.listCapacity("B"));
        two.appendAll(groups("B", 5));
        assertEquals(6, two.listCapacity("B"));
    }

    @Test
    void singleObjectPlusAppendedListIsExactlySized() {
        ReceiverGroups<String, Object> cached = groups("A", 1);
        cached.appendAll(groups("A", 2, "A", 3, "A", 4));
        assertEquals(4, cached.listCapacity("A"));
        assertEquals(List.of(1, 2, 3, 4), contents(cached).get("A"));
    }

    /**
     * Beyond the linear-scan threshold keys are found through the index; the
     * order of keys and objects and the single-object form are kept across
     * add, appendAll and the index rebuilds.
     */
    @Test
    void manyKeysKeepOrderThroughTheIndex() {
        int keyCount = 20 * ReceiverGroups.INDEX_THRESHOLD;
        ReceiverGroups<String, Object> cached = new ReceiverGroups<>();
        ReceiverGroups<String, Object> more = new ReceiverGroups<>();
        List<String> expectedKeys = new ArrayList<>();
        for (int i = 0; i < keyCount; ++i) {
            cached.add("k" + i, i);
            expectedKeys.add("k" + i);
            assertEquals(i >= ReceiverGroups.INDEX_THRESHOLD, cached.isIndexed());
        }
        for (int i = keyCount + keyCount / 2 - 1; i >= keyCount / 2; --i) {
            more.add("k" + i, -i);
        }
        for (int i = keyCount + keyCount / 2 - 1; i >= keyCount; --i) {
            expectedKeys.add("k" + i);
        }
        cached.appendAll(more);
        Map<String, List<Object>> m = contents(cached);
        assertEquals(expectedKeys, new ArrayList<>(m.keySet()));
        assertEquals(keyCount + keyCount / 2, cached.keyCount());
        assertEquals(2L * keyCount, cached.objectCount());
        assertEquals(List.of(0), m.get("k0"));
        assertSame(0, cached.singleObject("k0"));
        int half = keyCount / 2;
        assertEquals(List.of(half, -half), m.get("k" + half));
        assertEquals(List.of(-keyCount), m.get("k" + keyCount));
        assertEquals(-1, cached.listCapacity("absent"));
        assertNull(cached.singleObject("absent"));
    }

    /**
     * A seeded random sequence of add and appendAll over keys of which 32
     * share one hash code (concatenations of "Aa" and "BB"), so the index
     * probes along one chain, matches an insertion-ordered map of lists.
     */
    @Test
    void randomSequenceWithCollidingKeysMatchesAModel() {
        List<String> pool = new ArrayList<>(List.of(""));
        for (int i = 0; i < 5; ++i) {
            List<String> longer = new ArrayList<>();
            pool.forEach(s -> {
                longer.add(s + "Aa");
                longer.add(s + "BB");
            });
            pool = longer;
        }
        for (int i = 0; i < 30; ++i) {
            pool.add("n" + i);
        }
        Random random = new Random(115);
        // starts packed, as a receiver variable's grouping does
        ReceiverGroups<String, Object> cached = packed(
                pool.get(0), -1, pool.get(1), -2, pool.get(0), -3);
        Map<String, List<Object>> model = Maps.newLinkedHashMap();
        model.put(pool.get(0), new ArrayList<>(List.of(-1, -3)));
        model.put(pool.get(1), new ArrayList<>(List.of(-2)));
        List<ReceiverGroups<String, Object>> appended = new ArrayList<>();
        List<Map<String, List<Object>>> appendedModels = new ArrayList<>();
        int next = 0;
        for (int step = 0; step < 400; ++step) {
            if (random.nextBoolean()) {
                String key = pool.get(random.nextInt(pool.size()));
                cached.add(key, next);
                model.computeIfAbsent(key, k -> new ArrayList<>()).add(next);
                ++next;
            } else {
                List<Object> keyThenValues = new ArrayList<>();
                Map<String, List<Object>> moreModel = Maps.newLinkedHashMap();
                for (int n = random.nextInt(12); n > 0; --n) {
                    String key = pool.get(random.nextInt(pool.size()));
                    keyThenValues.add(key);
                    keyThenValues.add(next);
                    moreModel.computeIfAbsent(key, k -> new ArrayList<>()).add(next);
                    ++next;
                }
                // half of the appended groupings packed, as the analysis makes them
                ReceiverGroups<String, Object> more = random.nextBoolean()
                        ? packed(keyThenValues.toArray())
                        : groups(keyThenValues.toArray());
                cached.appendAll(more);
                moreModel.forEach((key, objs) ->
                        model.computeIfAbsent(key, k -> new ArrayList<>()).addAll(objs));
                appended.add(more);
                appendedModels.add(moreModel);
            }
            // lists of entries, so the order of keys counts too
            assertEquals(new ArrayList<>(model.entrySet()),
                    new ArrayList<>(contents(cached).entrySet()));
        }
        // nothing of an appended grouping is shared: later changes of the
        // cached grouping left every one of them unchanged
        for (int i = 0; i < appended.size(); ++i) {
            assertEquals(new ArrayList<>(appendedModels.get(i).entrySet()),
                    new ArrayList<>(contents(appended.get(i)).entrySet()));
        }
        assertEquals(model.size(), cached.keyCount());
        // the objects added plus the three the grouping started with
        assertEquals(next + 3, cached.objectCount());
        model.forEach((key, objs) -> assertEquals(
                objs.size() == 1 ? objs.get(0) : null, cached.singleObject(key)));
    }

    @Test
    void nullStateSkipsTheKey() {
        ReceiverGroups<String, Object> g = groups("A", 1, "B", 2, "B", 3, "C", 4);
        List<String> seen = new ArrayList<>();
        g.forEachGroup(new ReceiverGroups.Visitor<String, Object, String>() {
            @Override
            public String enter(String key) {
                return key.equals("B") ? null : key;
            }

            @Override
            public void accept(String key, Object obj) {
                seen.add(key + obj);
            }
        });
        assertEquals(List.of("A1", "C4"), seen);
    }

    /**
     * A packed grouping has the keys, objects and order of the grouping made
     * by adding the same objects, holds each group exactly sized, and opens
     * on the first change with every group unchanged.
     */
    @Test
    void packedGroupingMatchesAddedGroupingAndOpensOnChange() {
        Object[] keyThenValues = {"B", 1, "A", 2, "B", 3, "C", 4, "B", 5, "C", 7, "D", 8, "D", 9};
        ReceiverGroups<String, Object> g = packed(keyThenValues);
        // one array of 8 objects (48 bytes) beats lists of 3, 2 and 2 (80)
        assertTrue(g.isPacked());
        assertEquals(new ArrayList<>(contents(groups(keyThenValues)).entrySet()),
                new ArrayList<>(contents(g).entrySet()));
        assertEquals(4, g.keyCount());
        assertEquals(8, g.objectCount());
        assertEquals(0, g.slotOf("B"));
        assertEquals("C", g.keyAt(2));
        assertEquals(3, g.listCapacity("B"));
        assertEquals(-1, g.listCapacity("A"));
        assertSame(2, g.singleObject("A"));
        assertNull(g.singleObject("B"));
        g.add("A", 6);
        assertFalse(g.isPacked());
        assertEquals(3, g.listCapacity("B"));
        assertEquals(2, g.listCapacity("A"));
        assertEquals(2, g.listCapacity("C"));
        assertEquals(List.of(1, 3, 5), contents(g).get("B"));
        assertEquals(List.of(2, 6), contents(g).get("A"));
        assertEquals(List.of(4, 7), contents(g).get("C"));
        assertEquals(List.of("B", "A", "C", "D"), new ArrayList<>(contents(g).keySet()));
    }

    /**
     * Mostly single-object keys stay open, the repeated key in an exactly
     * sized list: one 24-byte list is smaller than a 32-byte array of all
     * four objects.
     */
    @Test
    void fewRepeatsGroupIntoListsWhenSmaller() {
        Object[] keyThenValues = {"B", 1, "A", 2, "C", 3, "B", 4};
        ReceiverGroups<String, Object> g = packed(keyThenValues);
        assertFalse(g.isPacked());
        assertEquals(new ArrayList<>(contents(groups(keyThenValues)).entrySet()),
                new ArrayList<>(contents(g).entrySet()));
        assertEquals(2, g.listCapacity("B"));
        assertSame(3, g.singleObject("C"));
    }

    @Test
    void packedGroupingWithManyKeysIsIndexed() {
        List<Object> keyThenValues = new ArrayList<>();
        int keyCount = 4 * ReceiverGroups.INDEX_THRESHOLD;
        for (int i = 0; i < 2 * keyCount; ++i) {
            keyThenValues.add("k" + (i % keyCount));
            keyThenValues.add(i);
        }
        ReceiverGroups<String, Object> g = packed(keyThenValues.toArray());
        assertTrue(g.isIndexed());
        assertEquals(keyCount, g.keyCount());
        assertEquals(List.of(3, 3 + keyCount), contents(g).get("k3"));
        assertEquals(keyCount - 1, g.slotOf("k" + (keyCount - 1)));
    }

    @Test
    void groupingOfSingleObjectKeysIsOpen() {
        ReceiverGroups<String, Object> g = packed("B", 1, "A", 2, "C", 3);
        assertFalse(g.isPacked());
        assertEquals(List.of("B", "A", "C"), new ArrayList<>(contents(g).keySet()));
        assertSame(2, g.singleObject("A"));
        assertEquals(-1, g.listCapacity("A"));
        g.add("A", 4);
        assertEquals(List.of(2, 4), contents(g).get("A"));
    }

    @Test
    void emptyPackedGroupingHasNoKeys() {
        ReceiverGroups<String, Object> g = packed();
        assertEquals(0, g.keyCount());
        assertEquals(0, g.objectCount());
        ReceiverGroups<String, Object> cached = groups("A", 1);
        cached.appendAll(g);
        assertEquals(1, cached.objectCount());
    }

    /**
     * The packed grouping iterates the objects twice; objects that change
     * between the two iterations are refused, not grouped wrongly.
     */
    @Test
    void packedGroupingRefusesObjectsThatChangeBetweenIterations() {
        Map<Integer, String> keyOf = Map.of(1, "A", 2, "B", 3, "A", 4, "B");
        // lists: an unknown key, too few objects, too many objects of a key
        assertThrows(ConcurrentModificationException.class,
                () -> ReceiverGroups.group(changing(List.of(1, 3), List.of(1, 2)), keyOf::get));
        assertThrows(ConcurrentModificationException.class,
                () -> ReceiverGroups.group(changing(List.of(1, 3, 2), List.of(1, 2)), keyOf::get));
        assertThrows(ConcurrentModificationException.class,
                () -> ReceiverGroups.group(changing(List.of(1, 3), List.of(1, 3, 1)), keyOf::get));
        // packed: too few objects, too many objects of a key
        assertThrows(ConcurrentModificationException.class,
                () -> ReceiverGroups.group(changing(List.of(1, 3, 2, 4), List.of(1, 3, 2)),
                        keyOf::get));
        assertThrows(ConcurrentModificationException.class,
                () -> ReceiverGroups.group(changing(List.of(1, 3, 2, 4), List.of(1, 3, 2, 4, 2)),
                        keyOf::get));
        // without a repeated key, one iteration only
        assertEquals(List.of(1, 2), contents(ReceiverGroups.<String, Object>group(
                changing(List.of(1, 2), List.of()), keyOf::get)).values().stream()
                .flatMap(List::stream).toList());
    }

    /**
     * @return an iterable yielding {@code first}, then {@code later} on every
     * further iteration.
     */
    private static Iterable<Integer> changing(List<Integer> first, List<Integer> later) {
        int[] iterations = {0};
        return () -> {
            Iterator<Integer> it = (iterations[0] == 0 ? first : later).iterator();
            ++iterations[0];
            return it;
        };
    }

    @Test
    void arrayObjectsAreRefused() {
        ReceiverGroups<String, Object> g = new ReceiverGroups<>();
        assertThrows(IllegalArgumentException.class, () -> g.add("A", new Object[0]));
        assertThrows(IllegalArgumentException.class,
                () -> ReceiverGroups.group(List.of((Object) new Object[0]), obj -> "A"));
    }
}
