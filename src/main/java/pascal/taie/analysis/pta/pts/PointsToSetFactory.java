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
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.SparseBitSet;

import java.util.function.Supplier;

/**
 * Provides static factory methods for {@link PointsToSet}.
 */
public class PointsToSetFactory {

    private final Supplier<PointsToSet> factory;

    private final Indexer<CSObj> objIndexer;

    public PointsToSetFactory(Indexer<CSObj> objIndexer) {
        this.objIndexer = objIndexer;
        factory = () -> new HybridBitPointsToSet(objIndexer, true);
    }

    /**
     * @return true if the set is a hybrid bit set in its large (bit set)
     * form, which iterates its objects in the order of their indexes
     */
    public boolean isLarge(PointsToSet pts) {
        return pts instanceof HybridBitPointsToSet hybrid
                && hybrid.set instanceof HybridBitSet<CSObj> set
                && set.isLarge();
    }

    /**
     * Packs a large points-to set made by this factory into the words of
     * {@link SparseBitSet#toPacked()}, a compact snapshot for sets that wait
     * long before they are read.
     *
     * @return the packed words, or {@code null} when the set is small or not
     * made by this factory
     */
    public long @Nullable [] toPackedLarge(PointsToSet pts) {
        if (pts instanceof HybridBitPointsToSet hybrid
                && hybrid.set instanceof HybridBitSet<CSObj> set) {
            return set.toPackedLarge(objIndexer);
        }
        return null;
    }

    /**
     * Restores the points-to set packed by {@link #toPackedLarge}: the result
     * equals a copy of the packed set, iteration order included.
     */
    public PointsToSet ofPackedLarge(long[] packed) {
        return new HybridBitPointsToSet(HybridBitSet.ofPackedLarge(objIndexer, packed));
    }

    /**
     * {@link #toPackedLarge} without a copy for a set stored packed (a set
     * shared through a {@link PointsToSetInterner} is): a snapshot that
     * shares its packed words.
     *
     * @return the snapshot, or {@code null} when {@link #toPackedLarge}
     * returns {@code null} or the set is not stored packed
     */
    public SparseBitSet.@Nullable PackedSnapshot packedLargeSnapshot(PointsToSet pts) {
        if (pts instanceof HybridBitPointsToSet hybrid
                && hybrid.set instanceof HybridBitSet<CSObj> set) {
            return set.packedLargeSnapshot(objIndexer);
        }
        return null;
    }

    /**
     * Restores the points-to set of a snapshot of
     * {@link #packedLargeSnapshot}: the result equals what
     * {@link #ofPackedLarge(long[])} makes of the words of
     * {@link #toPackedLarge} of the snapshotted set.
     */
    public PointsToSet ofPackedLarge(SparseBitSet.PackedSnapshot snapshot) {
        return new HybridBitPointsToSet(HybridBitSet.ofPackedLarge(objIndexer, snapshot));
    }

    public PointsToSet make() {
        return factory.get();
    }

    /**
     * Convenient method for making one-element points-to set.
     */
    public PointsToSet make(CSObj obj) {
        PointsToSet set = make();
        set.addObject(obj);
        return set;
    }
}
