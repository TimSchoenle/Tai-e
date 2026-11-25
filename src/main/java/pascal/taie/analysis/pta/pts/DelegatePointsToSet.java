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

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.util.collection.GenericBitSet;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.SetEx;

import java.util.Collections;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;

/**
 * Delegates points-to set to a concrete set implementation.
 */
public abstract class DelegatePointsToSet implements PointsToSet {

    /**
     * The set holding the objects. Public so that hot transfer functions
     * (e.g., TypeFilter) can operate on the underlying bit set directly.
     */
    public final SetEx<CSObj> set;

    /**
     * -1 while this set is mutable; once it is shared through a
     * {@link PointsToSetInterner}, the number of pointers holding it.
     * A shared set is never mutated, except that the interner may take a
     * set back from its table to change it in place for its only holder.
     */
    int holders = -1;

    /**
     * The {@link #sequenceHash()} of this set, valid once it is shared.
     */
    int internHash;

    DelegatePointsToSet(SetEx<CSObj> set) {
        this.set = set;
    }

    @Override
    public boolean isShared() {
        return holders >= 0;
    }

    private void checkMutable() {
        if (holders >= 0) {
            throw new IllegalStateException("shared points-to set is immutable");
        }
    }

    int sequenceHash() {
        return hybrid().sequenceHash();
    }

    boolean sameSequence(DelegatePointsToSet other) {
        return hybrid().sameSequence(other.hybrid());
    }

    boolean isLarge() {
        return hybrid().isLarge();
    }

    /**
     * @return true if {@code addAllDiff(pts)} would leave this set unchanged
     * in its form and elements.
     */
    boolean addAllDiffKeeps(DelegatePointsToSet pts) {
        return hybrid().addAllDiffKeeps(pts.hybrid());
    }

    /**
     * Stores a large set in its compact packed form; the contents, the
     * iteration order and the results of every query stay the same.
     */
    void pack() {
        hybrid().packLarge();
    }

    /**
     * @return true if this set is large and stored in its packed form.
     */
    boolean isPacked() {
        return hybrid().isPackedLarge();
    }

    /**
     * @return true if {@link #unionSummary}, {@link #isUnionOf} and
     * {@link #unionDiff} read {@code addAllDiff(pts)} without changing
     * this set (see {@link HybridBitSet#canSummarizeUnion}).
     */
    boolean canSummarizeUnion(DelegatePointsToSet pts) {
        return hybrid().canSummarizeUnion(pts.hybrid());
    }

    /**
     * @see HybridBitSet#unionSummary
     */
    long unionSummary(DelegatePointsToSet pts) {
        return hybrid().unionSummary(pts.hybrid());
    }

    /**
     * @see HybridBitSet#isUnionOf
     */
    boolean isUnionOf(DelegatePointsToSet a, DelegatePointsToSet b, long summary) {
        return hybrid().isUnionOf(a.hybrid(), b.hybrid(), summary);
    }

    /**
     * @return the difference {@code addAllDiff(pts)} would return, without
     * changing this set
     * @see HybridBitSet#unionDiff
     */
    PointsToSet unionDiff(DelegatePointsToSet pts) {
        return newSet(hybrid().unionDiff(pts.hybrid()));
    }

    /**
     * @return true if {@link #largeIntersection largeIntersection(bits)}
     * applies to this set
     * @see HybridBitSet#canIntersectLarge
     */
    public boolean canIntersectLarge(GenericBitSet<CSObj> bits) {
        return set instanceof HybridBitSet<CSObj> hybrid && hybrid.canIntersectLarge(bits);
    }

    /**
     * @return a new set of the objects of this set that are also in
     * {@code bits}, the set that {@link #copy()} and then keeping only
     * those objects in the bit set of the copy make; requires
     * {@link #canIntersectLarge canIntersectLarge(bits)}. This set does not
     * change.
     * @see HybridBitSet#largeIntersection
     */
    public PointsToSet largeIntersection(GenericBitSet<CSObj> bits) {
        return newSet(hybrid().largeIntersection(bits));
    }

    private HybridBitSet<CSObj> hybrid() {
        if (set instanceof HybridBitSet<CSObj> hybrid) {
            return hybrid;
        }
        throw new UnsupportedOperationException(
                "only hybrid bit points-to sets can be shared: " + getClass());
    }

    @Override
    public boolean addObject(CSObj obj) {
        checkMutable();
        return set.add(obj);
    }

    @Override
    public boolean addAll(PointsToSet pts) {
        checkMutable();
        if (pts instanceof DelegatePointsToSet other) {
            return set.addAll(other.set);
        } else {
            boolean changed = false;
            for (CSObj o : pts) {
                changed |= addObject(o);
            }
            return changed;
        }
    }

    @Override
    public void removeIf(Predicate<CSObj> filter) {
        checkMutable();
        set.removeIf(filter);
    }

    @Override
    public boolean contains(CSObj obj) {
        return set.contains(obj);
    }

    @Override
    public boolean isEmpty() {
        return set.isEmpty();
    }

    @Override
    public Set<CSObj> getObjects() {
        return Collections.unmodifiableSet(set);
    }

    @Override
    public Stream<CSObj> objects() {
        return set.stream();
    }

    @Override
    public int size() {
        return set.size();
    }

    @Override
    public String toString() {
        return set.toString();
    }

    @Override
    public PointsToSet addAllDiff(PointsToSet pts) {
        checkMutable();
        Set<CSObj> otherSet = pts instanceof DelegatePointsToSet other ?
                other.set : pts.getObjects();
        return newSet(set.addAllDiff(otherSet));
    }

    @Override
    public PointsToSet copy() {
        return newSet(set.copy());
    }

    protected abstract PointsToSet newSet(SetEx<CSObj> set);
}
