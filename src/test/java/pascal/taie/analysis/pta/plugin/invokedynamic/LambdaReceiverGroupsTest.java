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
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * The cached receiver grouping keeps first-seen order of types and of
 * objects per type when new points-to sets are appended.
 */
class LambdaReceiverGroupsTest {

    private static Map<String, List<Integer>> groups(Object... keyThenValues) {
        Map<String, List<Integer>> m = Maps.newLinkedHashMap();
        for (int i = 0; i < keyThenValues.length; i += 2) {
            m.computeIfAbsent((String) keyThenValues[i], k -> new ArrayList<>())
                    .add((Integer) keyThenValues[i + 1]);
        }
        return m;
    }

    @Test
    void appendKeepsFirstSeenOrderOfKeysAndObjects() {
        Map<String, List<Integer>> cached = groups("B", 1, "A", 2, "B", 3);
        Map<String, List<Integer>> first = groups("C", 4, "A", 5, "D", 6, "C", 7);
        LambdaAnalysis.appendGroups(cached, first);
        LambdaAnalysis.appendGroups(cached, groups("D", 8, "B", 9, "E", 10));
        assertEquals(List.of("B", "A", "C", "D", "E"), new ArrayList<>(cached.keySet()));
        assertEquals(List.of(1, 3, 9), cached.get("B"));
        assertEquals(List.of(2, 5), cached.get("A"));
        assertEquals(List.of(4, 7), cached.get("C"));
        assertEquals(List.of(6, 8), cached.get("D"));
        assertEquals(List.of(10), cached.get("E"));
    }

    @Test
    void newGroupIsCopiedNotShared() {
        Map<String, List<Integer>> cached = Maps.newLinkedHashMap();
        Map<String, List<Integer>> pts = groups("A", 1);
        LambdaAnalysis.appendGroups(cached, pts);
        assertNotSame(pts.get("A"), cached.get("A"));
        pts.get("A").add(2);
        assertEquals(List.of(1), cached.get("A"));
    }
}
