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

package pascal.taie.util.collection;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks {@link IntArraySets} against {@link HashSet} over random add and
 * contains sequences. A wrong probe loop would hang, hence the timeouts.
 */
class IntArraySetsTest {

    private static final int SEQUENCES = 200;

    @Test
    @Timeout(30)
    void randomSequencesAgreeWithHashSet() {
        Random random = new Random(20261123L);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int bound = switch (sequence % 4) {
                case 0 -> 16;
                case 1 -> 1_000;
                case 2 -> 1 << 20;
                default -> Integer.MAX_VALUE;
            };
            int operations = 1 + random.nextInt(sequence % 10 == 0 ? 20_000 : 300);
            runSequence(random, bound, operations);
        }
    }

    private static void runSequence(Random random, int bound, int operations) {
        Set<Integer> model = new HashSet<>();
        int[] set = null;
        for (int op = 0; op < operations; op++) {
            int element = random.nextInt(bound);
            if (random.nextInt(3) == 0) {
                assertEquals(model.contains(element),
                        IntArraySets.contains(set, element),
                        "contains " + element);
            } else {
                int[] after = IntArraySets.add(set, element);
                boolean added = model.add(element);
                assertEquals(added, after != null, "add " + element);
                if (after != null) {
                    set = after;
                }
            }
            assertEquals(model.size(), IntArraySets.size(set));
        }
        for (int element : model) {
            assertTrue(IntArraySets.contains(set, element), "lost " + element);
        }
    }

    @Test
    @Timeout(30)
    void denseRangeGrowsThroughEveryCapacity() {
        int[] set = null;
        for (int element = 0; element < 100_000; element++) {
            int[] after = IntArraySets.add(set, element);
            assertEquals(element + 1, IntArraySets.size(after));
            assertNull(IntArraySets.add(after, element));
            set = after;
        }
        for (int element = 0; element < 100_000; element++) {
            assertTrue(IntArraySets.contains(set, element));
        }
        assertFalse(IntArraySets.contains(set, 100_000));
    }

    @Test
    void extremesOfTheRange() {
        int largest = Integer.MAX_VALUE - 1;
        int[] set = IntArraySets.add(null, largest);
        set = IntArraySets.add(set, 0);
        assertTrue(IntArraySets.contains(set, largest));
        assertTrue(IntArraySets.contains(set, 0));
        assertFalse(IntArraySets.contains(set, 1));
        assertNull(IntArraySets.add(set, 0));
        assertThrows(IllegalArgumentException.class,
                () -> IntArraySets.add(null, -1));
        assertThrows(IllegalArgumentException.class,
                () -> IntArraySets.add(null, Integer.MAX_VALUE));
        assertThrows(IllegalArgumentException.class,
                () -> IntArraySets.contains(null, -1));
    }

    @Test
    void emptySetIsNull() {
        assertEquals(0, IntArraySets.size(null));
        assertFalse(IntArraySets.contains(null, 7));
    }

    @Test
    void addWithRoomReturnsTheSameArray() {
        int[] set = IntArraySets.add(null, 1);
        assertSame(set, IntArraySets.add(set, 2));
        for (int element = 3; element <= 10; element++) {
            set = IntArraySets.add(set, element);
        }
        // ten elements: a hash table of 16 slots with room left
        assertSame(set, IntArraySets.add(set, 11));
    }
}
