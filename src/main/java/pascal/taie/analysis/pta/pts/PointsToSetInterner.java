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

package pascal.taie.analysis.pta.pts;

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.util.collection.SparseBitSet;

/**
 * Shares equal points-to sets between pointers (hash-consing).
 * <p>
 * A pointer holds a shared set; a change of its points-to set builds the
 * new set on a copy, or in place when no other pointer holds the set, and
 * replaces the held set by the shared set equal to the result. A large set
 * held by several pointers that takes a large set first looks for the
 * result in the table and takes it from there without a copy; so does the
 * empty set that takes a large set, which returns the shared result as the
 * difference. Two sets are
 * equal here when they have the same form
 * (empty, singleton, small or large) and the same elements in iteration
 * order, so sharing never changes the iteration order of a pointer's set.
 * <p>
 * Each shared set counts the pointers holding it; a set that no pointer
 * holds any more leaves the table, so the table keeps no garbage alive.
 * A set in the table is never mutated.
 */
public final class PointsToSetInterner {

    private static final int INITIAL_CAPACITY = 1 << 10;

    private final DelegatePointsToSet empty;

    /**
     * Open addressing with linear probing; the capacity is a power of two.
     */
    private DelegatePointsToSet[] table;

    private int size;

    /**
     * Changes of a pointer's set through {@link #addAllDiff}, by the holder
     * count of the set before the change (see {@link Counters}).
     */
    private long unsharedWrites;

    private long soleWrites;

    private long twoHolderWrites;

    private long manyHolderWrites;

    /**
     * Changes made on a copy of the held set, and those of them whose copy
     * gave way to an equal shared set.
     */
    private long copies;

    private long copyHits;

    /**
     * Changes of a set held by two or more pointers that probed the table
     * for their result before copying, and those of them that found it.
     */
    private long probes;

    private long probeHits;

    /**
     * Whether the copies are counted by form (see {@link #formCopiesLine()});
     * the counts change no result and no order.
     */
    private boolean formCounting;

    /**
     * Copies made by {@link #addAllDiff}, and the objects in the copied
     * held sets, indexed by {@link #formIndex}.
     */
    private final long[] formCopies = new long[FORMS];

    private final long[] formCopyObjects = new long[FORMS];

    /**
     * The (held form, delta form) pairs, small or large each.
     */
    private static final int FORMS = 4;

    private static final String[] FORM_NAMES = {
            "small_small", "small_large", "large_small", "large_large"};

    /**
     * Changes of the empty set by a large set that took the shared set
     * equal to it, without a copy.
     */
    private long adoptions;

    public PointsToSetInterner(PointsToSetFactory factory) {
        this(factory, INITIAL_CAPACITY);
    }

    /**
     * @param capacity the initial number of slots, a power of two of at
     *                 least 2
     */
    PointsToSetInterner(PointsToSetFactory factory, int capacity) {
        if (capacity < 2 || Integer.bitCount(capacity) != 1) {
            throw new IllegalArgumentException(
                    "capacity must be a power of two of at least 2: " + capacity);
        }
        table = new DelegatePointsToSet[capacity];
        empty = intern(asDelegate(factory.make()));
        // pinned: the empty set never leaves the table
        empty.holders = 1;
    }

    /**
     * @return the shared empty set, counted as held by one more pointer.
     */
    public PointsToSet holdEmpty() {
        ++empty.holders;
        return empty;
    }

    /**
     * Copy-on-write form of {@code pt(pointer).addAllDiff(pts)}: a set that
     * other pointers hold too is never mutated, so the change is made on a
     * copy, which then replaces the held set by the shared set equal to it.
     * The copy undergoes exactly the operation the held set would, so the
     * pointer's new set and the returned difference are the same as
     * without sharing.
     * <p>
     * A shared set held by this pointer alone (not the empty set) is changed
     * in place instead: it leaves the table, takes the change and is shared
     * again, or gives way to the shared set equal to it. The result is the
     * same as on a copy, without copying the set. As without sharing, a
     * caller must not keep the set of a pointer across a change of that
     * pointer's set and expect the old contents.
     *
     * @return the difference between {@code pts} and the set the pointer
     * held before the call; the caller only reads it and does not keep it
     * past the next change of the pointer's set, as it may be the shared set
     * the pointer now holds.
     */
    public PointsToSet addAllDiff(Pointer pointer, PointsToSet pts) {
        PointsToSet held = pointer.getPointsToSet();
        if (held == null) {
            held = holdEmpty();
            pointer.setPointsToSet(held);
        }
        if (covers(held, pts)) {
            return empty;
        }
        countWrite(held);
        // the empty set, pinned at one, counts at least two once held
        if (held instanceof DelegatePointsToSet sole && sole.holders == 1) {
            return addAllDiffInPlace(pointer, sole, pts);
        }
        if (held == empty) {
            DelegatePointsToSet adopted = findAdoptable(pts);
            if (adopted != null) {
                ++adoptions;
                hold(adopted);
                release(empty);
                pointer.setPointsToSet(adopted);
                return adopted;
            }
        }
        if (held instanceof DelegatePointsToSet shared && shared.holders >= 2) {
            DelegatePointsToSet delta = asDelegate(pts);
            if (shared.canSummarizeUnion(delta)) {
                ++probes;
                DelegatePointsToSet found = findUnion(shared, delta);
                if (found != null) {
                    ++probeHits;
                    PointsToSet diff = shared.unionDiff(delta);
                    hold(found);
                    release(shared);
                    pointer.setPointsToSet(found);
                    return diff;
                }
            }
        }
        if (formCounting) {
            int form = formIndex(held, pts);
            ++formCopies[form];
            formCopyObjects[form] += held.size();
        }
        PointsToSet next = held.copy();
        PointsToSet diff = next.addAllDiff(pts);
        ++copies;
        pointer.setPointsToSet(replace(held, next));
        return diff;
    }

    /**
     * The empty set that takes a large set {@code pts} becomes a set of the
     * form and elements of {@code pts}, and the difference is such a set too
     * (see {@link pascal.taie.util.collection.HybridBitSet#addAllDiff}): a
     * shared set equal to {@code pts} serves as both, without the two copies.
     * The returned difference is then shared, so never mutated.
     *
     * @return the shared set equal to the large set {@code pts}, or null if
     * {@code pts} is not large or the table holds no such set
     */
    @Nullable
    private DelegatePointsToSet findAdoptable(PointsToSet pts) {
        DelegatePointsToSet delta = asDelegate(pts);
        if (!delta.isLarge()) {
            return null;
        }
        return table[probe(delta, delta.sequenceHash())];
    }

    private void countWrite(PointsToSet held) {
        // covers() has checked that held is a DelegatePointsToSet
        int holders = ((DelegatePointsToSet) held).holders;
        if (holders < 1) {
            ++unsharedWrites;
        } else if (holders == 1) {
            ++soleWrites;
        } else if (holders == 2) {
            ++twoHolderWrites;
        } else {
            ++manyHolderWrites;
        }
    }

    /**
     * Changes the shared set that only {@code pointer} holds in place and
     * shares the result again.
     */
    private PointsToSet addAllDiffInPlace(
            Pointer pointer, DelegatePointsToSet sole, PointsToSet pts) {
        remove(sole);
        sole.holders = -1;
        PointsToSet diff = sole.addAllDiff(pts);
        DelegatePointsToSet shared = intern(sole);
        hold(shared);
        pointer.setPointsToSet(shared);
        return diff;
    }

    /**
     * Probes the table for the set that {@code held.addAllDiff(pts)} would
     * make of a copy of {@code held}, without building it: its hash comes
     * from the state of {@code held} and one pass over the words of
     * {@code pts}; requires {@code held.canSummarizeUnion(pts)}.
     *
     * @return the shared set equal to that set, or null if the table holds
     * none
     */
    @Nullable
    private DelegatePointsToSet findUnion(DelegatePointsToSet held, DelegatePointsToSet pts) {
        long summary = held.unionSummary(pts);
        int hash = SparseBitSet.unionHash(summary);
        int mask = table.length - 1;
        for (int i = slot(hash, mask); table[i] != null; i = (i + 1) & mask) {
            DelegatePointsToSet e = table[i];
            if (e.internHash == hash && e.isUnionOf(held, pts, summary)) {
                return e;
            }
        }
        return null;
    }

    /**
     * @return true if {@code held.addAllDiff(pts)} would leave {@code held}
     * unchanged in its form and elements, so no copy is needed.
     */
    private static boolean covers(PointsToSet held, PointsToSet pts) {
        return asDelegate(held).addAllDiffKeeps(asDelegate(pts));
    }

    /**
     * Replaces the set held by one pointer with the shared set equal to
     * {@code next}, which this call takes over.
     */
    private PointsToSet replace(PointsToSet old, PointsToSet next) {
        DelegatePointsToSet shared = intern(asDelegate(next));
        if (shared != next) {
            ++copyHits;
        }
        if (shared != old) {
            hold(shared);
            release(old);
        }
        return shared;
    }

    /**
     * Counts one more pointer holding the shared set {@code shared}. A set
     * held by two or more pointers is never changed in place, so it is
     * stored packed (see {@link DelegatePointsToSet#pack()}); a sole holder
     * that changes it later restores its blocks.
     */
    private static void hold(DelegatePointsToSet shared) {
        if (++shared.holders >= 2) {
            shared.pack();
        }
    }

    /**
     * Gives the pointer a mutable copy of the shared set it holds and drops
     * its hold on the shared set, which leaves the table once no pointer
     * holds it. A later change through {@link #addAllDiff} shares the
     * pointer's set again.
     *
     * @return the pointer's points-to set afterwards: the copy, or the set
     * itself if it is not shared
     * @throws IllegalArgumentException if the pointer has no points-to set
     */
    public PointsToSet unshare(Pointer pointer) {
        PointsToSet held = pointer.getPointsToSet();
        if (held == null) {
            throw new IllegalArgumentException(pointer + " has no points-to set");
        }
        if (!held.isShared()) {
            return held;
        }
        PointsToSet copy = held.copy();
        pointer.setPointsToSet(copy);
        release(held);
        return copy;
    }

    /**
     * @return the number of shared sets in the table.
     */
    public int size() {
        return size;
    }

    /**
     * @return the number of slots of the table.
     */
    public int capacity() {
        return table.length;
    }

    /**
     * @return the counts of the changes made through {@link #addAllDiff}
     * so far.
     */
    public Counters counters() {
        return new Counters(unsharedWrites, soleWrites, twoHolderWrites,
                manyHolderWrites, copies, copyHits, probes, probeHits, adoptions);
    }

    /**
     * Counts of the changes that {@link #addAllDiff} made to a pointer's
     * set (calls that left the set unchanged are not counted). The holder
     * count of the shared empty set includes its pin, so the first change of
     * a pointer that holds it alone counts as held by two.
     *
     * @param unsharedWrites   changes of a set that is not shared
     * @param soleWrites       changes of a shared set held by the pointer
     *                         alone, made in place
     * @param twoHolderWrites  changes of a shared set held by two
     * @param manyHolderWrites changes of a shared set held by three or more
     * @param copies           changes made on a copy of the held set
     * @param copyHits         copies that gave way to an equal shared set
     * @param probes           changes of a large set held by two or more,
     *                         by a large set, that probed the table for the
     *                         result before copying
     * @param probeHits        probes that found the result shared, and took
     *                         it without a copy
     * @param adoptions        changes of the empty set by a large set that
     *                         took the shared set equal to that set, and
     *                         returned it as the difference, without a copy
     */
    public record Counters(long unsharedWrites, long soleWrites,
                           long twoHolderWrites, long manyHolderWrites,
                           long copies, long copyHits,
                           long probes, long probeHits, long adoptions) {
    }

    /**
     * Starts counting the copies of {@link #addAllDiff} by the forms of
     * the held set and of the delta.
     */
    public void enableFormCounters() {
        formCounting = true;
    }

    /**
     * @return the copies counted by form, as
     * {@code copies_<held>_<delta>=<copies>/<objects copied>} pairs, or the
     * empty text if they are not counted.
     */
    public String formCopiesLine() {
        if (!formCounting) {
            return "";
        }
        StringBuilder line = new StringBuilder();
        for (int i = 0; i < FORMS; ++i) {
            if (i > 0) {
                line.append(' ');
            }
            line.append("copies_").append(FORM_NAMES[i]).append('=')
                    .append(formCopies[i]).append('/').append(formCopyObjects[i]);
        }
        return line.toString();
    }

    private static int formIndex(PointsToSet held, PointsToSet pts) {
        return (asDelegate(held).isLarge() ? 2 : 0) + (asDelegate(pts).isLarge() ? 1 : 0);
    }

    private static DelegatePointsToSet asDelegate(PointsToSet set) {
        if (set instanceof DelegatePointsToSet delegate) {
            return delegate;
        }
        throw new UnsupportedOperationException(
                "cannot share points-to set " + set.getClass());
    }

    private void release(PointsToSet old) {
        if (old instanceof DelegatePointsToSet delegate && delegate.holders > 0
                && --delegate.holders == 0) {
            remove(delegate);
        }
    }

    /**
     * @return the shared set equal to {@code set}, or null if the table
     * holds none; holder counts are left as they are.
     */
    @Nullable
    PointsToSet find(PointsToSet set) {
        DelegatePointsToSet delegate = asDelegate(set);
        return table[probe(delegate, delegate.sequenceHash())];
    }

    /**
     * @return the slot of the shared set equal to {@code set}, or else the
     * free slot where it belongs.
     */
    private int probe(DelegatePointsToSet set, int hash) {
        int mask = table.length - 1;
        int i = slot(hash, mask);
        for (DelegatePointsToSet e; (e = table[i]) != null; i = (i + 1) & mask) {
            if (e.internHash == hash && e.sameSequence(set)) {
                return i;
            }
        }
        return i;
    }

    private DelegatePointsToSet intern(DelegatePointsToSet set) {
        if (set.holders >= 0) {
            return set;
        }
        int hash = set.sequenceHash();
        int i = probe(set, hash);
        DelegatePointsToSet found = table[i];
        if (found != null) {
            return found;
        }
        set.internHash = hash;
        set.holders = 0;
        table[i] = set;
        if (++size * 2 > table.length) {
            grow();
        }
        return set;
    }

    private void remove(DelegatePointsToSet set) {
        int mask = table.length - 1;
        int i = slot(set.internHash, mask);
        while (table[i] != set) {
            if (table[i] == null) {
                return; // not in the table
            }
            i = (i + 1) & mask;
        }
        // backward-shift deletion keeps every probe sequence unbroken
        int hole = i;
        for (int j = (i + 1) & mask; table[j] != null; j = (j + 1) & mask) {
            int home = slot(table[j].internHash, mask);
            boolean stays = hole <= j
                    ? hole < home && home <= j
                    : hole < home || home <= j;
            if (!stays) {
                table[hole] = table[j];
                hole = j;
            }
        }
        table[hole] = null;
        --size;
    }

    private void grow() {
        DelegatePointsToSet[] old = table;
        table = new DelegatePointsToSet[old.length * 2];
        int mask = table.length - 1;
        for (DelegatePointsToSet e : old) {
            if (e != null) {
                int i = slot(e.internHash, mask);
                while (table[i] != null) {
                    i = (i + 1) & mask;
                }
                table[i] = e;
            }
        }
    }

    private static int slot(int hash, int mask) {
        int h = hash * 0x9E3779B9;
        return (h ^ (h >>> 16)) & mask;
    }
}
