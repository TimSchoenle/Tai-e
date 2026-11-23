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
 * An array with at most {@link #LINEAR_CAPACITY} element slots keeps its
 * elements in slots {@code 1..size} and is searched linearly (capacities
 * 2, 4, 8). A larger array is an open-addressing hash table: its element-slot
 * count is a power of two, an element's home slot comes from a multiplicative
 * (Fibonacci) hash, collisions probe linearly, and the table doubles before an
 * insertion would raise its load above 3/4, so a table is between 3/8 and 3/4
 * full once it exists. Elements are never removed.
 */
public final class IntArraySets {

    /**
     * Largest element-slot count that is searched linearly.
     */
    private static final int LINEAR_CAPACITY = 8;

    private static final int FIRST_CAPACITY = 2;

    /**
     * The table grows when {@code (size + 1) * MAX_LOAD_DENOMINATOR}
     * exceeds {@code capacity * MAX_LOAD_NUMERATOR}.
     */
    private static final int MAX_LOAD_NUMERATOR = 3;

    private static final int MAX_LOAD_DENOMINATOR = 4;

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
     */
    public static int[] add(int[] set, int element) {
        int key = keyOf(element);
        if (set == null) {
            int[] created = new int[1 + FIRST_CAPACITY];
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
                int[] grown = Arrays.copyOf(set, 1 + 2 * capacity);
                grown[size + 1] = key;
                grown[0] = size + 1;
                return grown;
            }
            return insertAbsent(rehash(set, 2 * LINEAR_CAPACITY), key);
        }
        int slot = probe(set, key);
        if (set[slot] == key) {
            return null;
        }
        if ((size + 1L) * MAX_LOAD_DENOMINATOR > (long) capacity * MAX_LOAD_NUMERATOR) {
            return insertAbsent(rehash(set, 2 * capacity), key);
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
        int mask = table.length - 2;
        int shift = Integer.numberOfLeadingZeros(table.length - 1) + 1;
        int i = ((key - 1) * HASH_MULTIPLIER) >>> shift;
        while (true) {
            int value = table[1 + i];
            if (value == 0 || value == key) {
                return 1 + i;
            }
            i = (i + 1) & mask;
        }
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
