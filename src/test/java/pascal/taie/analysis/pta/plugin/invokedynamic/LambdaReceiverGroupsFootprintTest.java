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

import java.lang.ref.Reference;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Heap bytes a receiver grouping holds per key, measured over many
 * groupings whose keys and objects are shared, so only the grouping's own
 * structure is counted. A map entry per key (a LinkedHashMap per grouping)
 * costs about 90 bytes per key at three keys and 190 at one key; the
 * parallel arrays about 32 and 80 (with compressed oops: a 32-byte grouping
 * object plus two arrays of 24 bytes at one key, of 32 bytes at three keys).
 */
class LambdaReceiverGroupsFootprintTest {

    private static final int GROUPINGS = 100_000;

    private static final String[] KEYS = {"A", "B", "C"};

    private static final Object OBJ = new Object();

    @Test
    void threeSingleObjectKeysTakeUnder48BytesPerKey() {
        double perKey = bytesPerKey(3);
        System.out.println("[spd] receiver groups bytes per key (3 keys): " + perKey);
        assertTrue(perKey < 48, "bytes per key: " + perKey);
    }

    @Test
    void oneSingleObjectKeyTakesUnder120Bytes() {
        double perKey = bytesPerKey(1);
        System.out.println("[spd] receiver groups bytes per key (1 key): " + perKey);
        assertTrue(perKey < 120, "bytes per key: " + perKey);
    }

    /**
     * A group of two objects is held in an exactly sized array without a
     * list object around it: a 32-byte grouping, two arrays of 32 bytes for
     * the three keys and a 24-byte array per group, 56 bytes per key (80
     * with a 24-byte list object per group).
     */
    @Test
    void threeTwoObjectKeysTakeUnder66BytesPerKey() {
        double perKey = bytesPerKey(3, 2);
        System.out.println("[spd] receiver groups bytes per key (3 keys of 2 objects): " + perKey);
        assertTrue(perKey < 66, "bytes per key: " + perKey);
    }

    /**
     * A packed grouping of the same objects holds them in one array: a
     * 32-byte grouping, a 32-byte key array, a 40-byte array of the six
     * objects and a 32-byte array of group ends, 45 bytes per key.
     */
    @Test
    void packedThreeTwoObjectKeysTakeUnder52BytesPerKey() {
        double perKey = groupedBytesPerKey(2);
        System.out.println("[spd] packed receiver groups bytes per key (3 keys of 2 objects): "
                + perKey);
        assertTrue(perKey < 52, "bytes per key: " + perKey);
    }

    /**
     * Single-object keys are grouped open, as by adding them: 32 bytes per
     * key (packed, a 32-byte object array and a 32-byte array of group ends
     * would make it 43).
     */
    @Test
    void groupedThreeSingleObjectKeysTakeUnder38BytesPerKey() {
        double perKey = groupedBytesPerKey(1);
        System.out.println("[spd] grouped receiver groups bytes per key (3 keys): " + perKey);
        assertTrue(perKey < 38, "bytes per key: " + perKey);
    }

    /**
     * Groups {@code objsPerKey} rounds of one object per key with
     * {@link ReceiverGroups#group}.
     */
    private static double groupedBytesPerKey(int objsPerKey) {
        Object[] objs = new Object[KEYS.length * objsPerKey];
        Map<Object, String> keyOf = new IdentityHashMap<>();
        for (int i = 0; i < objs.length; ++i) {
            objs[i] = new Object();
            keyOf.put(objs[i], KEYS[i % KEYS.length]);
        }
        List<Object> objList = List.of(objs);
        long before = usedAfterGc();
        Object[] held = new Object[GROUPINGS];
        long array = usedAfterGc() - before;
        for (int i = 0; i < GROUPINGS; ++i) {
            held[i] = ReceiverGroups.group(objList, keyOf::get);
        }
        long used = usedAfterGc() - before - array;
        Reference.reachabilityFence(held);
        return (double) used / ((long) GROUPINGS * KEYS.length);
    }

    private static double bytesPerKey(int keyCount) {
        return bytesPerKey(keyCount, 1);
    }

    /**
     * Adds {@code objsPerKey} rounds of one object per key, as a receiver
     * variable's points-to set of interleaved types does.
     */
    private static double bytesPerKey(int keyCount, int objsPerKey) {
        long before = usedAfterGc();
        Object[] held = new Object[GROUPINGS];
        long array = usedAfterGc() - before;
        for (int i = 0; i < GROUPINGS; ++i) {
            ReceiverGroups<String, Object> g = new ReceiverGroups<>();
            for (int round = 0; round < objsPerKey; ++round) {
                for (int k = 0; k < keyCount; ++k) {
                    g.add(KEYS[k], OBJ);
                }
            }
            held[i] = g;
        }
        long used = usedAfterGc() - before - array;
        Reference.reachabilityFence(held);
        return (double) used / ((long) GROUPINGS * keyCount);
    }

    private static long usedAfterGc() {
        Runtime runtime = Runtime.getRuntime();
        for (int i = 0; i < 3; ++i) {
            System.gc();
        }
        return runtime.totalMemory() - runtime.freeMemory();
    }
}
