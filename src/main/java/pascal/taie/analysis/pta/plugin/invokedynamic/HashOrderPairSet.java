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

import pascal.taie.util.collection.HybridHashSet;

import java.util.Arrays;
import java.util.ConcurrentModificationException;
import java.util.Set;

/**
 * A set of pairs {@code (a, b)}, equal when both components are equal, kept
 * in flat arrays instead of one pair object and one hash node per element,
 * that iterates in exactly the order of a {@link HybridHashSet} of pair
 * objects whose hash code is {@link #hash} and to which the same pairs were
 * added in the same order.
 * <p>
 * The order of that set: up to {@link HybridHashSet#getThreshold()} elements
 * it keeps them in insertion order, and the first add at that size (also of
 * a present element) moves them, in insertion order, into a
 * {@link java.util.HashSet} of twice that capacity, which iterates by bucket
 * and within a bucket in insertion order. This set emulates the buckets of
 * {@link java.util.HashMap}: the spread hash, the resize at three quarters of
 * the capacity, the order-preserving split of a resize, and the resize instead
 * of a tree bin while the table is small. A bucket that would become a tree
 * bin (whose order depends on the tree) is not emulated: the set then replays
 * its pairs, in insertion order, into a real {@link HybridHashSet}, which
 * builds the same tables as the emulated set did, and uses it from then on.
 * Elements are never removed.
 * <p>
 * The {@link java.util.HashMap} constants below and the hybrid set's move
 * to twice its small size are copies; {@code HashOrderPairSetTest} compares
 * this set with a real {@link HybridHashSet} on every path (small set, move,
 * resizes, resize instead of a tree bin, replay) and is the guard for a JDK
 * or {@link HybridHashSet} change.
 *
 * @param <A> type of the first component
 * @param <B> type of the second component
 */
abstract class HashOrderPairSet<A, B> {

    /**
     * Size up to which a {@link HybridHashSet} keeps insertion order.
     */
    private static final int SMALL_SIZE = new HybridHashSet<>().getThreshold();

    /**
     * Capacity of the hash set a {@link HybridHashSet} moves to:
     * {@code HashSet(2 * SMALL_SIZE)}, rounded up to a power of two as
     * {@link java.util.HashMap} rounds its initial capacity.
     */
    private static final int LARGE_CAPACITY = tableSizeFor(2 * SMALL_SIZE);

    /**
     * {@link java.util.HashMap}'s bucket length from which an added node
     * turns the bucket into a tree bin (its {@code TREEIFY_THRESHOLD}).
     */
    private static final int TREEIFY_THRESHOLD = 8;

    /**
     * {@link java.util.HashMap}'s smallest table that gets tree bins; a
     * smaller table is resized instead (its {@code MIN_TREEIFY_CAPACITY}).
     */
    private static final int MIN_TREEIFY_CAPACITY = 64;

    static {
        // the move into the hash set replays the small elements without
        // the resize and tree checks, which they cannot reach
        if (SMALL_SIZE > TREEIFY_THRESHOLD || SMALL_SIZE > threshold(LARGE_CAPACITY)) {
            throw new IllegalStateException("small set size " + SMALL_SIZE
                    + " reaches a resize or a tree bin of the large set");
        }
    }

    /**
     * Visitor of the pairs of a set.
     */
    interface Visitor<A, B> {
        void visit(A a, B b);
    }

    /**
     * The pairs in insertion order: the first component of element
     * {@code i} at {@code 2 * i}, the second at {@code 2 * i + 1};
     * {@code null} after the switch to {@link #replay}.
     */
    private Object[] pairs = new Object[2];

    /**
     * Number of elements in {@link #pairs}.
     */
    private int size;

    /**
     * Per bucket of the emulated hash table, the first element of the
     * bucket plus one ({@code 0}: empty); {@code null} while the set keeps
     * insertion order.
     */
    private int[] table;

    /**
     * Per element, the next element of its bucket plus one ({@code 0}:
     * last); set together with {@link #table}.
     */
    private int[] next;

    /**
     * The real set that holds the pairs once a bucket would become a tree
     * bin; {@code null} before.
     */
    private Set<Pair<A, B>> replay;

    /**
     * @return the hash code of the pair object of {@code (a, b)}.
     */
    protected abstract int hash(A a, B b);

    /**
     * Adds the pair {@code (a, b)}.
     *
     * @return whether the set did not contain the pair.
     */
    boolean add(A a, B b) {
        if (replay != null) {
            return replay.add(new Pair<>(a, b, hash(a, b)));
        }
        if (table == null) {
            if (size < SMALL_SIZE) {
                if (indexOf(a, b) >= 0) {
                    return false;
                }
                append(a, b);
                return true;
            }
            startHashing();
        }
        return hashedAdd(a, b);
    }

    /**
     * @return whether the set contains the pair {@code (a, b)}. Unlike
     * {@link #add} of a present pair, this never moves the set into its
     * hashed form, so it does not change the iteration order.
     */
    boolean contains(A a, B b) {
        if (replay != null) {
            return replay.contains(new Pair<>(a, b, hash(a, b)));
        }
        if (table == null) {
            return indexOf(a, b) >= 0;
        }
        for (int e = table[spread(a, b) & (table.length - 1)]; e != 0; e = next[e - 1]) {
            if (matches(e - 1, a, b)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return the number of pairs.
     */
    int size() {
        return replay != null ? replay.size() : size;
    }

    /**
     * Visits every pair in the order of the emulated set. {@code visitor}
     * must not add to this set.
     */
    void forEach(Visitor<? super A, ? super B> visitor) {
        if (replay != null) {
            int expected = replay.size();
            for (Pair<A, B> pair : replay) {
                visitor.visit(pair.a, pair.b);
            }
            checkUnchanged(expected, replay.size());
        } else if (table == null) {
            int expected = size;
            for (int i = 0; i < expected; ++i) {
                visitor.visit(first(i), second(i));
            }
            checkUnchanged(expected, size);
        } else {
            int expected = size;
            int[] buckets = table;
            for (int head : buckets) {
                for (int e = head; e != 0; e = next[e - 1]) {
                    visitor.visit(first(e - 1), second(e - 1));
                }
            }
            checkUnchanged(expected, size);
        }
    }

    private static void checkUnchanged(int expected, int actual) {
        if (expected != actual) {
            throw new ConcurrentModificationException(
                    "pair set changed from " + expected + " to " + actual
                            + " elements while visited");
        }
    }

    private int indexOf(A a, B b) {
        for (int i = 0; i < size; ++i) {
            if (matches(i, a, b)) {
                return i;
            }
        }
        return -1;
    }

    private boolean matches(int index, A a, B b) {
        return a.equals(pairs[2 * index]) && b.equals(pairs[2 * index + 1]);
    }

    @SuppressWarnings("unchecked")
    private A first(int index) {
        return (A) pairs[2 * index];
    }

    @SuppressWarnings("unchecked")
    private B second(int index) {
        return (B) pairs[2 * index + 1];
    }

    /**
     * Stores {@code (a, b)} as element {@link #size} and counts it; grows
     * {@link #next} with {@link #pairs} once the set hashes.
     */
    private void append(A a, B b) {
        if (2 * size == pairs.length) {
            int capacity = size + Math.max(1, size >> 1);
            pairs = Arrays.copyOf(pairs, 2 * capacity);
            if (next != null) {
                next = Arrays.copyOf(next, capacity);
            }
        }
        pairs[2 * size] = a;
        pairs[2 * size + 1] = b;
        ++size;
    }

    /**
     * Moves the elements, in insertion order, into an emulated table of
     * {@link #LARGE_CAPACITY} buckets, as a {@link HybridHashSet} moves its
     * small set into its hash set.
     */
    private void startHashing() {
        table = new int[LARGE_CAPACITY];
        next = new int[pairs.length / 2];
        for (int i = 0; i < size; ++i) {
            int bucket = spread(first(i), second(i)) & (table.length - 1);
            int last = lastOf(bucket);
            link(last, bucket, i);
        }
    }

    /**
     * Adds {@code (a, b)} as {@link java.util.HashMap#put} adds a new key:
     * at the end of its bucket, then the resize (or the replay) for a
     * bucket that would become a tree bin, then the resize for the size.
     */
    private boolean hashedAdd(A a, B b) {
        int bucket = spread(a, b) & (table.length - 1);
        int length = 0;
        int last = 0;
        for (int e = table[bucket]; e != 0; e = next[e - 1]) {
            if (matches(e - 1, a, b)) {
                return false;
            }
            last = e;
            ++length;
        }
        int index = size;
        append(a, b);
        link(last, bucket, index);
        if (length >= TREEIFY_THRESHOLD) {
            if (table.length < MIN_TREEIFY_CAPACITY) {
                resize();
            } else {
                startReplay();
                return true;
            }
        }
        if (size > threshold(table.length)) {
            resize();
        }
        return true;
    }

    private int lastOf(int bucket) {
        int last = 0;
        for (int e = table[bucket]; e != 0; e = next[e - 1]) {
            last = e;
        }
        return last;
    }

    /**
     * Puts element {@code index} after element {@code last - 1} of
     * {@code bucket}, or first when {@code last} is {@code 0}.
     */
    private void link(int last, int bucket, int index) {
        if (last == 0) {
            table[bucket] = index + 1;
        } else {
            next[last - 1] = index + 1;
        }
        next[index] = 0;
    }

    /**
     * Doubles the table as {@link java.util.HashMap}'s resize does: each
     * bucket splits into the bucket of the same index and the bucket one old
     * capacity higher, both in the old bucket's order.
     */
    private void resize() {
        int[] old = table;
        int oldCapacity = old.length;
        int[] resized = new int[2 * oldCapacity];
        for (int j = 0; j < oldCapacity; ++j) {
            int loHead = 0;
            int loTail = 0;
            int hiHead = 0;
            int hiTail = 0;
            for (int e = old[j]; e != 0; e = next[e - 1]) {
                if ((spread(first(e - 1), second(e - 1)) & oldCapacity) == 0) {
                    if (loTail == 0) {
                        loHead = e;
                    } else {
                        next[loTail - 1] = e;
                    }
                    loTail = e;
                } else {
                    if (hiTail == 0) {
                        hiHead = e;
                    } else {
                        next[hiTail - 1] = e;
                    }
                    hiTail = e;
                }
            }
            if (loTail != 0) {
                next[loTail - 1] = 0;
                resized[j] = loHead;
            }
            if (hiTail != 0) {
                next[hiTail - 1] = 0;
                resized[j + oldCapacity] = hiHead;
            }
        }
        table = resized;
    }

    /**
     * Replays the elements, in insertion order, into a real
     * {@link HybridHashSet}, which then holds the set.
     */
    private void startReplay() {
        Set<Pair<A, B>> set = new HybridHashSet<>();
        for (int i = 0; i < size; ++i) {
            A a = first(i);
            B b = second(i);
            set.add(new Pair<>(a, b, hash(a, b)));
        }
        replay = set;
        pairs = null;
        table = null;
        next = null;
        size = 0;
    }

    /**
     * @return the hash of {@code (a, b)} spread as
     * {@link java.util.HashMap} spreads a key's hash code.
     */
    private int spread(A a, B b) {
        int h = hash(a, b);
        return h ^ (h >>> 16);
    }

    /**
     * @return the size above which {@link java.util.HashMap} resizes a
     * table of {@code capacity} buckets (of at least 16), with its default
     * load factor.
     */
    private static int threshold(int capacity) {
        return capacity - (capacity >>> 2);
    }

    private static int tableSizeFor(int capacity) {
        return capacity <= 1 ? 1 : Integer.highestOneBit(capacity - 1) << 1;
    }

    /**
     * A pair object of the replay set: equal when both components are
     * equal, with the hash code of the set.
     */
    private static final class Pair<A, B> {

        private final A a;

        private final B b;

        private final int hash;

        private Pair(A a, B b, int hash) {
            this.a = a;
            this.b = b;
            this.hash = hash;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof Pair<?, ?> that)) {
                return false;
            }
            return a.equals(that.a) && b.equals(that.b);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }
}
