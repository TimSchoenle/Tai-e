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
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

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
}
