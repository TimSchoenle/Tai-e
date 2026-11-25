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
        // the same extremes in a hash table
        int[] table = null;
        for (int element = 1; element <= 20; element++) {
            table = IntArraySets.add(table, element);
        }
        table = IntArraySets.add(IntArraySets.add(table, largest), 0);
        assertEquals(22, IntArraySets.size(table));
        assertTrue(IntArraySets.contains(table, largest));
        assertTrue(IntArraySets.contains(table, 0));
        assertNull(IntArraySets.add(table, largest));
        assertNull(IntArraySets.add(table, 0));
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
        int[] set = IntArraySets.add(IntArraySets.add(null, 1), 2);
        // two elements: a linear array of 3 slots with room left
        assertSame(set, IntArraySets.add(set, 3));
        for (int element = 4; element <= 10; element++) {
            set = IntArraySets.add(set, element);
        }
        // ten elements: a hash table of 13 slots with room left
        assertSame(set, IntArraySets.add(set, 11));
    }

    /**
     * An int array of even length has no alignment padding (16-byte header,
     * 4-byte elements, 8-byte alignment), so every slot paid for is usable.
     */
    @Test
    void everyArrayHasEvenLength() {
        Random random = new Random(20261125L);
        int[] set = null;
        for (int op = 0; op < 20_000; op++) {
            int[] after = IntArraySets.add(set, random.nextInt(Integer.MAX_VALUE));
            if (after != null) {
                set = after;
                assertEquals(0, set.length % 2,
                        "odd length " + set.length + " at size " + set[0]);
            }
        }
    }

    /**
     * A hash table holds at most 85 % of its slots and grows by about a
     * quarter, so it stays at least 60 % full once it exists.
     */
    @Test
    void hashTableStaysDense() {
        int[] set = null;
        int growths = 0;
        for (int element = 0; element < 100_000; element++) {
            int[] after = IntArraySets.add(set, element * 7919);
            int capacity = after.length - 1;
            int size = after[0];
            if (capacity > 9) {
                assertTrue(size * 100L <= capacity * 85L,
                        size + " elements in " + capacity + " slots");
                assertTrue(size * 100L >= capacity * 60L,
                        size + " elements in " + capacity + " slots");
                if (after != set && set.length - 1 > 9) {
                    ++growths;
                    // a quarter more, plus rounding up to an odd count
                    assertTrue(capacity * 4L <= (set.length - 1) * 5L + 8,
                            "grew from " + (set.length - 1) + " to " + capacity);
                }
            }
            set = after;
        }
        assertTrue(growths > 10, "only " + growths + " table growths");
    }
}
