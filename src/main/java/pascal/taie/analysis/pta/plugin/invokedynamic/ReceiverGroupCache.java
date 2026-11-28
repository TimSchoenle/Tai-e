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

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.Supplier;

/**
 * The receiver groupings of the lambda receiver variables, one per variable
 * or, when shared, one per points-to set object of the solver.
 * <p>
 * Unshared, each variable holds its own grouping, extended in place by every
 * difference ({@link ReceiverGroups#appendAll}), as without this class.
 * <p>
 * Shared, a grouping is found by the identity of the solver's set object
 * that the variables hold. Identity is not content: the solver changes a
 * set that one pointer holds alone in place. Since points-to sets only grow,
 * a grouping made from a set's content holds a subset of that set object's
 * content ever after, so a grouping is used for a set only when it holds as
 * many objects as the set (then equal content). Sharing therefore requires
 * that no points-to set ever loses an object (LambdaAnalysis rejects the
 * interactive taint mode, which removes taint objects). An entry counts the
 * variables holding it and leaves the table when the last one leaves, so the
 * table keeps no set alive that no variable holds.
 *
 * @param <K> type of keys of the groupings
 * @param <V> type of objects of the groupings
 */
final class ReceiverGroupCache<K, V> {

    /**
     * A grouping and the variables holding it.
     *
     * @param <K> type of keys
     * @param <V> type of objects
     */
    static final class Entry<K, V> {

        private final ReceiverGroups<K, V> groups;

        /**
         * The number of distinct objects of {@link #groups}; read only when
         * shared.
         */
        private int objects;

        private int holders = 1;

        /**
         * The set object this entry is found by in the table, or null if it
         * is not in the table.
         */
        private @Nullable Object key;

        private Entry(ReceiverGroups<K, V> groups, int objects) {
            this.groups = groups;
            this.objects = objects;
        }

        ReceiverGroups<K, V> groups() {
            return groups;
        }
    }

    /**
     * The result of {@link #advance}: the entry the variable holds now, and
     * whether the slots of its old grouping keep their keys in it (the old
     * grouping was extended in place or copied); otherwise the slots of the
     * variable's targets must be mapped through the keys.
     */
    record Advance<K, V>(Entry<K, V> entry, boolean slotsKept) {
    }

    private final boolean shared;

    private final Map<Object, Entry<K, V>> bySet = new IdentityHashMap<>();

    private long extensions;

    private long joins;

    private long copies;

    private long rebuilds;

    ReceiverGroupCache(boolean shared) {
        this.shared = shared;
    }

    /**
     * @return whether groupings are shared by points-to set object.
     */
    boolean isShared() {
        return shared;
    }

    /**
     * @return the entry a variable that first needs a grouping holds, for
     * its points-to set {@code set} of {@code setSize} objects: shared, the
     * entry of {@code set} if it holds as many objects, otherwise a new
     * entry of {@code grouper}'s grouping of the set.
     */
    Entry<K, V> attach(Object set, int setSize, Supplier<ReceiverGroups<K, V>> grouper) {
        if (!shared) {
            return new Entry<>(grouper.get(), setSize);
        }
        Entry<K, V> found = bySet.get(set);
        if (found != null && found.objects == setSize) {
            ++found.holders;
            return found;
        }
        Entry<K, V> entry = new Entry<>(grouper.get(), setSize);
        rekey(entry, set);
        return entry;
    }

    /**
     * Moves a variable holding {@code held} to its new points-to set
     * {@code set} of {@code setSize} objects, the old one plus the
     * difference grouped as {@code delta} of {@code deltaSize} objects.
     * Unshared: {@code delta} is appended to the variable's grouping.
     * Shared: the variable joins the entry of {@code set} if it holds as
     * many objects; otherwise its grouping, if it already holds
     * {@code setSize} objects (made while the set was being propagated), is
     * kept, or else extended by {@code delta}, in place if the variable holds
     * it alone, otherwise on a copy. If neither count fits (the solver broke
     * its propagation order), the grouping is made anew by {@code regroup}
     * (counted); the caller then gives known slots only to the types of
     * {@code delta}, as the per-variable grouping, which would lack the
     * other objects, did.
     */
    Advance<K, V> advance(Entry<K, V> held, Object set, int setSize,
                          ReceiverGroups<K, V> delta, int deltaSize,
                          Supplier<ReceiverGroups<K, V>> regroup) {
        if (!shared) {
            held.groups.appendAll(delta);
            return new Advance<>(held, true);
        }
        Entry<K, V> found = bySet.get(set);
        if (found != null && found != held && found.objects == setSize) {
            ++found.holders;
            release(held);
            ++joins;
            return new Advance<>(found, false);
        }
        boolean covered = held.objects == setSize;
        if (!covered && held.objects + deltaSize != setSize) {
            release(held);
            Entry<K, V> rebuilt = new Entry<>(regroup.get(), setSize);
            rekey(rebuilt, set);
            ++rebuilds;
            return new Advance<>(rebuilt, false);
        }
        Entry<K, V> next = held;
        if (!covered) {
            if (held.holders == 1) {
                held.groups.appendAll(delta);
                held.objects = setSize;
                ++extensions;
            } else {
                ReceiverGroups<K, V> copy = new ReceiverGroups<>();
                copy.appendAll(held.groups);
                copy.appendAll(delta);
                release(held);
                next = new Entry<>(copy, setSize);
                ++copies;
            }
        }
        rekey(next, set);
        return new Advance<>(next, true);
    }

    /**
     * Makes {@code entry}, which holds the content of {@code set}, the
     * entry {@code set} is found by, in place of an entry of {@code set}
     * that holds fewer objects (which stays with its holders, out of the
     * table).
     */
    private void rekey(Entry<K, V> entry, Object set) {
        if (entry.key == set) {
            return;
        }
        unlink(entry);
        Entry<K, V> stale = bySet.put(set, entry);
        if (stale != null) {
            stale.key = null;
        }
        entry.key = set;
    }

    /**
     * Counts one variable less holding {@code entry}; the last one takes it
     * out of the table.
     */
    private void release(Entry<K, V> entry) {
        if (--entry.holders == 0) {
            unlink(entry);
        }
    }

    private void unlink(Entry<K, V> entry) {
        Object key = entry.key;
        if (key != null) {
            bySet.remove(key, entry);
            entry.key = null;
        }
    }

    /**
     * @return the number of entries in the table (shared only).
     */
    int size() {
        return bySet.size();
    }

    /**
     * @return the number of variables holding {@code entry}.
     */
    static int holders(Entry<?, ?> entry) {
        return entry.holders;
    }

    /**
     * @return the counts of {@link #advance} by outcome.
     */
    String countsLine() {
        return "sharedGroupings=" + bySet.size() + " extensions=" + extensions +" joins=" + joins
                + " copies=" + copies + " rebuilds=" + rebuilds;
    }

    void clear() {
        bySet.clear();
    }
}
