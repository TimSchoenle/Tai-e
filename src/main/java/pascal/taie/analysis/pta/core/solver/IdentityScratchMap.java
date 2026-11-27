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

package pascal.taie.analysis.pta.core.solver;

import org.jspecify.annotations.Nullable;

import java.util.Objects;

/**
 * A reusable map keyed by identity, for the scratch state of one call site
 * in {@link DefaultSolver} (option {@code call-batching}): open addressing
 * with linear probing, at most half full, its keys kept in first-put order.
 * {@link #clear()} costs the number of keys, so one instance serves every
 * call site without allocating.
 */
final class IdentityScratchMap {

    private static final int MIN_CAPACITY = 16;

    private Object[] keys = new Object[MIN_CAPACITY];

    private Object[] values = new Object[MIN_CAPACITY];

    /**
     * The slots of the keys in first-put order.
     */
    private int[] order = new int[MIN_CAPACITY / 2];

    private int size;

    /**
     * @return the value of {@code key}, or null if it has none.
     */
    @Nullable Object get(Object key) {
        int mask = keys.length - 1;
        int i = slotOf(key, mask);
        Object k;
        while ((k = keys[i]) != null) {
            if (k == key) {
                return values[i];
            }
            i = (i + 1) & mask;
        }
        return null;
    }

    /**
     * Puts a key that is not in the map.
     *
     * @throws NullPointerException  if {@code key} or {@code value} is null
     *                               (a null slot marks a free slot, and a
     *                               null value an absent key)
     * @throws IllegalStateException if {@code key} is already in the map
     */
    void put(Object key, Object value) {
        Objects.requireNonNull(key, "key");
        Objects.requireNonNull(value, "value");
        if ((size + 1) * 2 > keys.length) {
            grow();
        }
        insert(key, value);
    }

    /**
     * @return the number of keys.
     */
    int size() {
        return size;
    }

    /**
     * @return the {@code i}-th key in first-put order.
     */
    Object keyAt(int i) {
        if (i < 0 || i >= size) {
            throw new IndexOutOfBoundsException(i);
        }
        return keys[order[i]];
    }

    /**
     * Removes every key.
     */
    void clear() {
        for (int i = 0; i < size; ++i) {
            int slot = order[i];
            keys[slot] = null;
            values[slot] = null;
        }
        size = 0;
    }

    private void insert(Object key, Object value) {
        int mask = keys.length - 1;
        int i = slotOf(key, mask);
        Object k;
        while ((k = keys[i]) != null) {
            if (k == key) {
                throw new IllegalStateException("key already in the map: " + key);
            }
            i = (i + 1) & mask;
        }
        keys[i] = key;
        values[i] = value;
        order[size++] = i;
    }

    private void grow() {
        Object[] oldKeys = keys;
        Object[] oldValues = values;
        int[] oldOrder = order;
        int oldSize = size;
        keys = new Object[oldKeys.length * 2];
        values = new Object[oldKeys.length * 2];
        order = new int[oldKeys.length];
        size = 0;
        for (int i = 0; i < oldSize; ++i) {
            int slot = oldOrder[i];
            insert(oldKeys[slot], oldValues[slot]);
        }
    }

    private static int slotOf(Object key, int mask) {
        int h = System.identityHashCode(key);
        return (h ^ (h >>> 16)) & mask;
    }
}
