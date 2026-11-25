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
import java.util.ConcurrentModificationException;
import java.util.Objects;
import java.util.function.Function;

/**
 * Objects grouped by a key, keys and the objects of each key in first-seen
 * order. Add-only.
 * <p>
 * Keys are held in an array in first-seen order, without a map entry per
 * key. Keys are found by a linear scan up to {@link #INDEX_THRESHOLD} keys,
 * beyond that through an open-addressing index of key positions. Keys are
 * non-null and compared by {@code equals}.
 * <p>
 * The groups have one of two layouts. A grouping made by {@link #group}
 * with keys of two or more objects is packed when that is smaller (see
 * {@link #pack}): the objects of all keys in
 * one array of exactly their number, key by key, and the end of each key's
 * objects in an int array. Any other grouping is open: per key, the group's
 * only object (most groups hold one object), or an array of two or more
 * objects, the objects first and free slots (null) after them. A packed
 * grouping opens when {@link #add} or {@link #appendAll} changes it, each
 * list then exactly sized. Objects are never arrays, so no object can be
 * mistaken for a list.
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
     * Open layout ({@link #ends} null): per slot of {@link #keys}, the
     * group's only object, or an array of two or more objects followed by
     * nulls. Packed layout: the objects of all keys, the group of slot
     * {@code i} from {@code ends[i - 1]} (0 for the first slot) to
     * {@code ends[i]}.
     */
    private Object[] groups = EMPTY;

    /**
     * Packed layout: per slot of {@link #keys}, the end (exclusive) of its
     * group in {@link #groups}. Null in the open layout.
     */
    private int @Nullable [] ends;

    private int size;

    /**
     * Above {@link #INDEX_THRESHOLD} keys: open-addressing table (power of
     * two length, at most half full) of key positions plus one; 0 marks a
     * free slot. Null up to the threshold.
     */
    private int @Nullable [] index;

    /**
     * @return the objects of {@code objs} grouped by {@code keyOf}. If every
     * key has one object, the grouping is open, made in one iteration of
     * {@code objs} with the arrays the constructor and {@link #add} make.
     * Otherwise {@code objs} is iterated a second time to place the objects,
     * packed if that is smaller ({@link #pack}), and must yield the same
     * objects in the same order both times (the caller guarantees it).
     * @throws ConcurrentModificationException if the second iteration yields
     *                                         a different number of objects
     *                                         for some key
     */
    static <K, V> ReceiverGroups<K, V> group(
            Iterable<? extends V> objs, Function<? super V, ? extends K> keyOf) {
        ReceiverGroups<K, V> g = new ReceiverGroups<>();
        // objects per slot, made at the first key seen a second time
        int[] counts = null;
        for (V obj : objs) {
            checkObject(obj);
            K key = keyOf.apply(obj);
            int pos = g.indexOf(key);
            if (pos < 0) {
                g.append(key, obj);
                if (counts != null) {
                    if (counts.length < g.size) {
                        counts = Arrays.copyOf(counts, g.keys.length);
                    }
                    counts[g.size - 1] = 1;
                }
            } else {
                if (counts == null) {
                    counts = new int[g.keys.length];
                    Arrays.fill(counts, 0, g.size, 1);
                }
                ++counts[pos];
            }
        }
        if (counts == null) {
            return g;
        }
        g.pack(objs, keyOf, counts);
        return g;
    }

    /**
     * Completes the open grouping of which {@link #group} has seen the keys
     * and the first object of each, {@code counts} objects per slot, placing
     * the objects in the order of a second iteration of {@code objs}: in the
     * packed layout if its one array of all objects is smaller than the
     * lists of the open layout, otherwise in exactly sized lists.
     */
    private void pack(Iterable<? extends V> objs, Function<? super V, ? extends K> keyOf,
                      int[] counts) {
        int total = 0;
        long listBytes = 0;
        for (int i = 0; i < size; ++i) {
            total += counts[i];
            if (counts[i] > 1) {
                listBytes += arrayBytes(counts[i]);
            }
        }
        if (arrayBytes(total) < listBytes) {
            placePacked(objs, keyOf, counts, total);
        } else {
            placeLists(objs, keyOf, counts, total);
        }
    }

    /**
     * @return the heap bytes of an Object[] of {@code length} with
     * compressed references, used only to choose a layout.
     */
    private static long arrayBytes(int length) {
        return (16L + 4L * length + 7) & ~7L;
    }

    private void placePacked(Iterable<? extends V> objs,
                             Function<? super V, ? extends K> keyOf, int[] counts, int total) {
        int[] next = new int[size];
        int end = 0;
        for (int i = 0; i < size; ++i) {
            next[i] = end;
            end += counts[i];
            // counts become the ends of the groups
            counts[i] = end;
        }
        Object[] items = new Object[total];
        int placed = 0;
        for (V obj : objs) {
            checkObject(obj);
            int pos = indexOf(keyOf.apply(obj));
            if (pos < 0 || next[pos] == counts[pos]) {
                throw changed();
            }
            items[next[pos]++] = obj;
            ++placed;
        }
        if (placed != total) {
            throw changed();
        }
        groups = items;
        ends = counts;
    }

    private void placeLists(Iterable<? extends V> objs,
                            Function<? super V, ? extends K> keyOf, int[] counts, int total) {
        int[] next = new int[size];
        int placed = 0;
        for (V obj : objs) {
            checkObject(obj);
            int pos = indexOf(keyOf.apply(obj));
            if (pos < 0 || next[pos] == counts[pos]) {
                throw changed();
            }
            // a group of one object holds it since the first iteration
            if (counts[pos] > 1) {
                Object[] list = next[pos] == 0
                        ? new Object[counts[pos]]
                        : (Object[]) groups[pos];
                list[next[pos]] = obj;
                groups[pos] = list;
            }
            ++next[pos];
            ++placed;
        }
        if (placed != total) {
            throw changed();
        }
    }

    private static ConcurrentModificationException changed() {
        return new ConcurrentModificationException(
                "objects changed between the two iterations");
    }

    /**
     * Adds {@code obj} at the end of the group of {@code key}.
     */
    void add(K key, V obj) {
        checkObject(obj);
        openLayout();
        int pos = indexOf(key);
        if (pos < 0) {
            append(key, obj);
        } else {
            groups[pos] = plus(groups[pos], obj);
        }
    }

    /**
     * Appends the groups of {@code more} in place: a group of a new key comes
     * after the existing keys, held as its object or copied into an exactly
     * sized list; the objects of a known key come after that key's objects.
     * Nothing of {@code more} is shared.
     */
    void appendAll(ReceiverGroups<K, V> more) {
        openLayout();
        int[] moreEnds = more.ends;
        int start = 0;
        for (int i = 0; i < more.size; ++i) {
            Object key = more.keys[i];
            if (moreEnds != null) {
                int end = moreEnds[i];
                appendObjects(key, more.groups, start, end);
                start = end;
            } else if (more.groups[i] instanceof Object[] list) {
                appendObjects(key, list, 0, fill(list));
            } else {
                appendObject(key, more.groups[i]);
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
    <S> void forEachGroup(Visitor<? super K, ? super V, S> visitor) {
        for (int i = 0; i < size; ++i) {
            visitGroup(i, visitor);
        }
    }

    /**
     * {@link #forEachGroup} restricted to the first {@code count} slots of
     * {@code slots} (key positions, ascending): visits those keys in that
     * order, which is their first-seen order. A visitor whose
     * {@link Visitor#enter} returns null for every key left out sees the
     * same calls of {@link Visitor#accept} as with {@link #forEachGroup}.
     */
    <S> void forEachGroup(int[] slots, int count, Visitor<? super K, ? super V, S> visitor) {
        for (int i = 0; i < count; ++i) {
            visitGroup(Objects.checkIndex(slots[i], size), visitor);
        }
    }

    @SuppressWarnings("unchecked")
    private <S> void visitGroup(int slot, Visitor<? super K, ? super V, S> visitor) {
        S state = visitor.enter((K) keys[slot]);
        if (state == null) {
            return;
        }
        int[] packedEnds = ends;
        if (packedEnds != null) {
            int end = packedEnds[slot];
            for (int j = startOf(packedEnds, slot); j < end; ++j) {
                visitor.accept(state, (V) groups[j]);
            }
            return;
        }
        Object group = groups[slot];
        if (group instanceof Object[] list) {
            for (int j = 0; j < list.length && list[j] != null; ++j) {
                visitor.accept(state, (V) list[j]);
            }
        } else {
            visitor.accept(state, (V) group);
        }
    }

    /**
     * @return the key at position {@code slot} (below {@link #keyCount}).
     */
    @SuppressWarnings("unchecked")
    K keyAt(int slot) {
        Objects.checkIndex(slot, size);
        return (K) keys[slot];
    }

    /**
     * @return the position of {@code key} in first-seen order, or -1 if it
     * is absent.
     */
    int slotOf(K key) {
        return indexOf(key);
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
            count += sizeOf(i);
        }
        return count;
    }

    /**
     * @return the object of {@code key} if its group holds one object,
     * otherwise null. For tests of the representation.
     */
    @Nullable
    @SuppressWarnings("unchecked")
    V singleObject(K key) {
        int pos = indexOf(key);
        if (pos < 0 || sizeOf(pos) != 1) {
            return null;
        }
        int[] packedEnds = ends;
        return (V) (packedEnds != null ? groups[startOf(packedEnds, pos)] : groups[pos]);
    }

    /**
     * @return the number of slots of {@code key}'s list (in the packed
     * layout, its number of objects), or -1 if the key holds a single
     * object or is absent. For tests of the representation.
     */
    int listCapacity(K key) {
        int pos = indexOf(key);
        if (pos < 0) {
            return -1;
        }
        if (ends != null) {
            int count = sizeOf(pos);
            return count == 1 ? -1 : count;
        }
        return groups[pos] instanceof Object[] list ? list.length : -1;
    }

    /**
     * @return whether keys are found through the index. For tests of the
     * representation.
     */
    boolean isIndexed() {
        return index != null;
    }

    /**
     * @return whether the groups have the packed layout. For tests of the
     * representation.
     */
    boolean isPacked() {
        return ends != null;
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
     * Turns the packed layout into the open one, each group of two or more
     * objects into an exactly sized list.
     */
    private void openLayout() {
        int[] packedEnds = ends;
        if (packedEnds == null) {
            return;
        }
        Object[] items = groups;
        Object[] open = new Object[keys.length];
        int start = 0;
        for (int i = 0; i < size; ++i) {
            int end = packedEnds[i];
            open[i] = end - start == 1 ? items[start] : Arrays.copyOfRange(items, start, end);
            start = end;
        }
        groups = open;
        ends = null;
    }

    /**
     * Open layout: adds {@code obj} at the end of the group of {@code key}.
     */
    private void appendObject(Object key, Object obj) {
        int pos = indexOf(key);
        if (pos < 0) {
            append(key, obj);
        } else {
            groups[pos] = plus(groups[pos], obj);
        }
    }

    /**
     * Open layout: adds {@code src[from]} to {@code src[to - 1]} at the end
     * of the group of {@code key}, without sharing {@code src}.
     */
    private void appendObjects(Object key, Object[] src, int from, int to) {
        int count = to - from;
        if (count == 1) {
            appendObject(key, src[from]);
            return;
        }
        int pos = indexOf(key);
        if (pos < 0) {
            append(key, Arrays.copyOfRange(src, from, to));
            return;
        }
        Object group = groups[pos];
        Object[] list;
        int filled;
        if (group instanceof Object[] old) {
            filled = fill(old);
            int needed = filled + count;
            list = needed > old.length
                    ? Arrays.copyOf(old, Math.max(needed, old.length + (old.length >> 1)))
                    : old;
        } else {
            list = new Object[1 + count];
            list[0] = group;
            filled = 1;
        }
        System.arraycopy(src, from, list, filled, count);
        groups[pos] = list;
    }

    /**
     * Open layout: adds {@code key}, absent so far, with {@code group} after
     * the existing keys.
     */
    private void append(Object key, Object group) {
        // appendKey may replace groups, so it runs before groups is read
        int pos = appendKey(key);
        groups[pos] = group;
    }

    /**
     * Open layout: adds {@code key}, absent so far, after the existing keys,
     * growing {@link #groups} with {@link #keys}.
     *
     * @return the position of {@code key}
     */
    private int appendKey(Object key) {
        Objects.requireNonNull(key);
        if (size == keys.length) {
            // the growth of java.util.ArrayList, from capacity one
            int capacity = size + Math.max(1, size >> 1);
            keys = Arrays.copyOf(keys, capacity);
            groups = Arrays.copyOf(groups, capacity);
        }
        keys[size] = key;
        ++size;
        int[] table = index;
        if (table != null && 2 * size <= table.length) {
            insert(table, size - 1);
        } else if (table != null || size > INDEX_THRESHOLD) {
            rebuildIndex();
        }
        return size - 1;
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

    /**
     * @return the number of objects of the group at {@code slot}.
     */
    private int sizeOf(int slot) {
        int[] packedEnds = ends;
        if (packedEnds != null) {
            return packedEnds[slot] - startOf(packedEnds, slot);
        }
        return groups[slot] instanceof Object[] list ? fill(list) : 1;
    }

    private static int startOf(int[] packedEnds, int slot) {
        return slot == 0 ? 0 : packedEnds[slot - 1];
    }

    /**
     * @return {@code group} (an object or a list) with {@code obj} added at
     * its end, a list grown as java.util.ArrayList grows.
     */
    private static Object plus(Object group, Object obj) {
        if (group instanceof Object[] list) {
            int filled = fill(list);
            Object[] grown = filled == list.length
                    ? Arrays.copyOf(list, filled + Math.max(1, filled >> 1))
                    : list;
            grown[filled] = obj;
            return grown;
        }
        return new Object[]{group, obj};
    }

    /**
     * @return the number of objects in {@code list}: its objects come first
     * and its free slots (null) after them.
     */
    private static int fill(Object[] list) {
        int low = 0;
        int high = list.length;
        while (low < high) {
            int mid = (low + high) >>> 1;
            if (list[mid] == null) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        return low;
    }

    private static void checkObject(Object obj) {
        Objects.requireNonNull(obj);
        if (obj instanceof Object[]) {
            throw new IllegalArgumentException(
                    "an array cannot be grouped: it would be taken for a list");
        }
    }
}
