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

import java.util.Arrays;

/**
 * Static operations on a grow-only set of non-negative ints held in a single
 * {@code int[]}, for a field that is mostly empty or small and should not pay
 * for a set object of its own.
 * <p>
 * Layout: {@code null} is the empty set. Otherwise slot 0 holds the size and
 * every other slot holds {@code element + 1}, where 0 marks a free slot.
 * Every element-slot count is odd, so every array has an even length and,
 * with the 16-byte array header of the JVMs in use (no compact object
 * headers), 4-byte slots and 8-byte alignment, no alignment padding.
 * An array with at most {@link #LINEAR_CAPACITY} element slots keeps its
 * elements in slots {@code 1..size} and is searched linearly (capacities
 * 1, 3, 5, 7, 9). A larger array is an open-addressing hash table of any odd
 * element-slot count: an element's home slot comes from a multiplicative
 * (Fibonacci) hash scaled to the slot count, collisions probe linearly with
 * wrap-around, and the table grows by about a quarter before an insertion
 * would raise its load above 85 %, so a table is about 68 % to 85 % full once
 * it exists. Elements are never removed.
 */
public final class IntArraySets {

    /**
     * Largest element-slot count that is searched linearly.
     */
    private static final int LINEAR_CAPACITY = 9;

    /**
     * Element slots a full linear array gains when it grows; even, so its
     * capacity stays odd.
     */
    private static final int LINEAR_STEP = 2;

    /**
     * The table grows when {@code (size + 1) * MAX_LOAD_DENOMINATOR}
     * exceeds {@code capacity * MAX_LOAD_NUMERATOR}.
     */
    private static final int MAX_LOAD_NUMERATOR = 17;

    private static final int MAX_LOAD_DENOMINATOR = 20;

    /**
     * A growing table gains at least {@code capacity / GROWTH_DIVISOR}
     * element slots.
     */
    private static final int GROWTH_DIVISOR = 4;

    /**
     * Largest array length the JVMs in use allocate.
     */
    private static final int MAX_ARRAY_LENGTH = Integer.MAX_VALUE - 8;

    /**
     * 2^32 divided by the golden ratio, the multiplier of Fibonacci hashing.
     */
    private static final int HASH_MULTIPLIER = 0x9E3779B9;

    private IntArraySets() {
    }

    /**
     * Adds an element.
     *
     * @param set     the set, {@code null} for the empty set
     * @param element the element, at least 0 and below {@link Integer#MAX_VALUE}
     * @return {@code null} if the set already contained the element; otherwise
     * the set with the element, which is {@code set} itself or a new array
     * that replaces it
     * @throws IllegalArgumentException if the element is out of range
     * @throws IllegalStateException    if the set would outgrow the array
     *                                  length limit
     */
    public static int[] add(int[] set, int element) {
        int key = keyOf(element);
        if (set == null) {
            int[] created = new int[2];
            created[0] = 1;
            created[1] = key;
            return created;
        }
        int size = set[0];
        int capacity = set.length - 1;
        if (capacity <= LINEAR_CAPACITY) {
            for (int i = 1; i <= size; i++) {
                if (set[i] == key) {
                    return null;
                }
            }
            if (size < capacity) {
                set[size + 1] = key;
                set[0] = size + 1;
                return set;
            }
            if (capacity < LINEAR_CAPACITY) {
                int[] grown = Arrays.copyOf(set, 1 + capacity + LINEAR_STEP);
                grown[size + 1] = key;
                grown[0] = size + 1;
                return grown;
            }
            return insertAbsent(rehash(set, grownCapacity(capacity, size + 1)), key);
        }
        int slot = probe(set, key);
        if (set[slot] == key) {
            return null;
        }
        if ((size + 1L) * MAX_LOAD_DENOMINATOR > (long) capacity * MAX_LOAD_NUMERATOR) {
            return insertAbsent(rehash(set, grownCapacity(capacity, size + 1)), key);
        }
        set[slot] = key;
        set[0] = size + 1;
        return set;
    }

    /**
     * @param set     the set, {@code null} for the empty set
     * @param element the element, at least 0 and below {@link Integer#MAX_VALUE}
     * @return whether the set contains the element
     * @throws IllegalArgumentException if the element is out of range
     */
    public static boolean contains(int[] set, int element) {
        int key = keyOf(element);
        if (set == null) {
            return false;
        }
        if (set.length - 1 <= LINEAR_CAPACITY) {
            for (int i = 1; i <= set[0]; i++) {
                if (set[i] == key) {
                    return true;
                }
            }
            return false;
        }
        return set[probe(set, key)] == key;
    }

    /**
     * @param set the set, {@code null} for the empty set
     * @return the number of elements of the set
     */
    public static int size(int[] set) {
        return set == null ? 0 : set[0];
    }

    private static int keyOf(int element) {
        if (element < 0 || element == Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                    "element out of range: " + element);
        }
        return element + 1;
    }

    /**
     * @return the array index of the slot of a hash table that holds
     * {@code key}, or of the free slot where {@code key} belongs
     */
    private static int probe(int[] table, int key) {
        int capacity = table.length - 1;
        // the high bits of the 32-bit hash, scaled to [0, capacity)
        int i = (int) (((key * HASH_MULTIPLIER) & 0xFFFF_FFFFL) * capacity >>> 32);
        while (true) {
            int value = table[1 + i];
            if (value == 0 || value == key) {
                return 1 + i;
            }
            if (++i == capacity) {
                i = 0;
            }
        }
    }

    /**
     * @return the odd element-slot count of the table that replaces a full
     * array of {@code capacity} element slots: at least a quarter larger,
     * and large enough to hold {@code size} elements within the load limit
     * @throws IllegalStateException if that table exceeds the array length
     *                               limit
     */
    private static int grownCapacity(int capacity, int size) {
        long grown = capacity + (long) (capacity / GROWTH_DIVISOR);
        long needed = (size * (long) MAX_LOAD_DENOMINATOR + MAX_LOAD_NUMERATOR - 1)
                / MAX_LOAD_NUMERATOR;
        long odd = Math.max(grown, needed) | 1L;
        if (1 + odd > MAX_ARRAY_LENGTH) {
            throw new IllegalStateException(
                    "set of " + size + " elements exceeds the array length limit");
        }
        return (int) odd;
    }

    /**
     * @return a hash table of {@code capacity} element slots holding every
     * element of {@code set}
     */
    private static int[] rehash(int[] set, int capacity) {
        int[] table = new int[1 + capacity];
        for (int i = 1; i < set.length; i++) {
            if (set[i] != 0) {
                insertAbsent(table, set[i]);
            }
        }
        return table;
    }

    private static int[] insertAbsent(int[] table, int key) {
        table[probe(table, key)] = key;
        table[0]++;
        return table;
    }
}
