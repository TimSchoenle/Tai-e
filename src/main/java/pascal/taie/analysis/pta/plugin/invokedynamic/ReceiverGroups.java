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

import org.jspecify.annotations.Nullable;

import java.util.Arrays;
import java.util.Objects;

/**
 * Objects grouped by a key, keys and the objects of each key in first-seen
 * order. Add-only. Most groups hold one object, so a group of one object is
 * held as the object itself; a second object of the key turns it into a
 * list.
 * <p>
 * Keys and groups are held in two parallel arrays in first-seen order,
 * without a map entry per key. Keys are found by a linear scan up to
 * {@link #INDEX_THRESHOLD} keys, beyond that through an open-addressing
 * index of key positions. Keys are non-null and compared by {@code equals}.
 *
 * @param <K> type of keys
 * @param <V> type of objects
 */
final class ReceiverGroups<K, V> {

    /**
     * The largest number of keys found by a linear scan.
     */
    static final int INDEX_THRESHOLD = 8;

    private static final Object[] EMPTY = {};

    /**
     * The keys in first-seen order; slots from {@link #size} on are free.
     */
    private Object[] keys = EMPTY;

    /**
     * Per slot of {@link #keys}: the group's only object, or a {@link Group}
     * of two or more. {@link Group} is private, so no object can be mistaken
     * for a group.
     */
    private Object[] groups = EMPTY;

    private int size;

    /**
     * Above {@link #INDEX_THRESHOLD} keys: open-addressing table (power of
     * two length, at most half full) of key positions plus one; 0 marks a
     * free slot. Null up to the threshold.
     */
    private int @Nullable [] index;

    /**
     * Adds {@code obj} at the end of the group of {@code key}.
     */
    void add(K key, V obj) {
        Objects.requireNonNull(obj);
        int pos = indexOf(key);
        if (pos < 0) {
            append(key, obj);
            return;
        }
        Object group = groups[pos];
        if (group instanceof Group list) {
            list.add(obj);
        } else {
            groups[pos] = new Group(group, obj);
        }
    }

    /**
     * Appends the groups of {@code more} in place: a group of a new key comes
     * after the existing keys, held as its object or copied into an exactly
     * sized list; the objects of a known key come after that key's objects.
     * Nothing of {@code more} is shared.
     */
    void appendAll(ReceiverGroups<K, V> more) {
        for (int i = 0; i < more.size; ++i) {
            Object key = more.keys[i];
            Object extra = more.groups[i];
            int pos = indexOf(key);
            if (pos < 0) {
                append(key, extra instanceof Group list ? list.copy() : extra);
                continue;
            }
            Object group = groups[pos];
            if (group instanceof Group list) {
                list.addAll(extra);
            } else {
                Group list = new Group(1 + sizeOf(extra));
                list.add(group);
                list.addAll(extra);
                groups[pos] = list;
            }
        }
    }

    /**
     * Visits the groups: per key, {@link #enter} once, then {@link #accept}
     * per object with the state {@code enter} returned.
     *
     * @param <K> type of keys
     * @param <V> type of objects
     * @param <S> type of the per-key state
     */
    interface Visitor<K, V, S> {

        /**
         * @return the state passed to {@link #accept} for the objects of
         * {@code key}, or null to skip the key.
         */
        @Nullable
        S enter(K key);

        void accept(S state, V obj);
    }

    /**
     * For each key in first-seen order, calls {@code visitor.enter} and, if
     * it returns a state, {@code visitor.accept} for each object of the key
     * in first-seen order.
     */
    @SuppressWarnings("unchecked")
    <S> void forEachGroup(Visitor<? super K, ? super V, S> visitor) {
        for (int i = 0; i < size; ++i) {
            S state = visitor.enter((K) keys[i]);
            if (state == null) {
                continue;
            }
            Object group = groups[i];
            if (group instanceof Group list) {
                for (int j = 0; j < list.size; ++j) {
                    visitor.accept(state, (V) list.elements[j]);
                }
            } else {
                visitor.accept(state, (V) group);
            }
        }
    }

    /**
     * @return the number of keys.
     */
    int keyCount() {
        return size;
    }

    /**
     * @return the number of objects over all keys.
     */
    long objectCount() {
        long count = 0;
        for (int i = 0; i < size; ++i) {
            count += sizeOf(groups[i]);
        }
        return count;
    }

    /**
     * @return the object of {@code key} if it is held as a single object
     * (not in a list), otherwise null. For tests of the representation.
     */
    @Nullable
    @SuppressWarnings("unchecked")
    V singleObject(K key) {
        int pos = indexOf(key);
        return pos < 0 || groups[pos] instanceof Group ? null : (V) groups[pos];
    }

    /**
     * @return the number of slots of {@code key}'s list, or -1 if the key
     * holds a single object or is absent. For tests of the representation.
     */
    int listCapacity(K key) {
        int pos = indexOf(key);
        return pos >= 0 && groups[pos] instanceof Group list ? list.elements.length : -1;
    }

    /**
     * @return whether keys are found through the index. For tests of the
     * representation.
     */
    boolean isIndexed() {
        return index != null;
    }

    /**
     * @return the position of {@code key} in {@link #keys}, or -1.
     */
    private int indexOf(Object key) {
        int[] table = index;
        if (table == null) {
            for (int i = 0; i < size; ++i) {
                if (key.equals(keys[i])) {
                    return i;
                }
            }
            return -1;
        }
        int mask = table.length - 1;
        // the table is at most half full, so a free slot ends the probe
        for (int slot = hash(key) & mask; ; slot = (slot + 1) & mask) {
            int entry = table[slot];
            if (entry == 0) {
                return -1;
            }
            if (key.equals(keys[entry - 1])) {
                return entry - 1;
            }
        }
    }

    /**
     * Adds {@code key}, absent so far, with {@code group} after the existing
     * keys.
     */
    private void append(Object key, Object group) {
        Objects.requireNonNull(key);
        if (size == keys.length) {
            // the growth of java.util.ArrayList, from capacity one
            int capacity = size + Math.max(1, size >> 1);
            keys = Arrays.copyOf(keys, capacity);
            groups = Arrays.copyOf(groups, capacity);
        }
        keys[size] = key;
        groups[size] = group;
        ++size;
        int[] table = index;
        if (table != null && 2 * size <= table.length) {
            insert(table, size - 1);
        } else if (table != null || size > INDEX_THRESHOLD) {
            rebuildIndex();
        }
    }

    /**
     * Builds the index at a quarter to a half full.
     */
    private void rebuildIndex() {
        int[] table = new int[Integer.highestOneBit(size) << 2];
        for (int i = 0; i < size; ++i) {
            insert(table, i);
        }
        index = table;
    }

    private void insert(int[] table, int pos) {
        int mask = table.length - 1;
        int slot = hash(keys[pos]) & mask;
        while (table[slot] != 0) {
            slot = (slot + 1) & mask;
        }
        table[slot] = pos + 1;
    }

    private static int hash(Object key) {
        int h = key.hashCode();
        // the spreading of java.util.HashMap
        return h ^ (h >>> 16);
    }

    private static int sizeOf(Object group) {
        return group instanceof Group list ? list.size : 1;
    }

    /**
     * An append-only list of two or more objects.
     */
    private static final class Group {

        private Object[] elements;

        private int size;

        private Group(int capacity) {
            elements = new Object[capacity];
        }

        private Group(Object first, Object second) {
            elements = new Object[]{first, second};
            size = 2;
        }

        private void add(Object obj) {
            if (size == elements.length) {
                // the growth of java.util.ArrayList
                elements = Arrays.copyOf(elements, size + Math.max(1, size >> 1));
            }
            elements[size++] = obj;
        }

        /**
         * Appends {@code group}: one object or the objects of a list.
         */
        private void addAll(Object group) {
            if (group instanceof Group list) {
                int needed = size + list.size;
                if (needed > elements.length) {
                    elements = Arrays.copyOf(elements,
                            Math.max(needed, elements.length + (elements.length >> 1)));
                }
                System.arraycopy(list.elements, 0, elements, size, list.size);
                size = needed;
            } else {
                add(group);
            }
        }

        private Group copy() {
            Group copy = new Group(size);
            System.arraycopy(elements, 0, copy.elements, 0, size);
            copy.size = size;
            return copy;
        }
    }
}
