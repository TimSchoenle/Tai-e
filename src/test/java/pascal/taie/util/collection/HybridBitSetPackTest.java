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

import org.junit.jupiter.api.Test;
import pascal.taie.util.Indexer;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Checks which sets {@link HybridBitSet#toPackedLarge} packs: only a large
 * sparse set whose own form and bits both belong to the expected indexer,
 * since {@link HybridBitSet#ofPackedLarge} restores exactly that form.
 */
class HybridBitSetPackTest {

    private static final class IdentityIndexer implements Indexer<Integer> {

        @Override
        public int getIndex(Integer o) {
            return o;
        }

        @Override
        public Integer getObject(int index) {
            return index;
        }
    }

    private final Indexer<Integer> indexer = new IdentityIndexer();

    private final Indexer<Integer> otherIndexer = new IdentityIndexer();

    @Test
    void largeSparseSetOfTheIndexerIsPackedAndRestored() {
        HybridBitSet<Integer> set = largeSparseSet(indexer);
        long[] packed = set.toPackedLarge(indexer);
        assertNotNull(packed);
        HybridBitSet<Integer> restored = HybridBitSet.ofPackedLarge(indexer, packed);
        assertEquals(order(set), order(restored));
        assertEquals(set, restored);
    }

    @Test
    void largeSparseBitsInADenseSetAreNotPacked() {
        // a dense hybrid set takes over the sparse bits of a large set it absorbs
        HybridBitSet<Integer> dense = new HybridBitSet<>(indexer, false);
        dense.addAllDiff(largeSparseSet(indexer));
        assertNull(dense.toPackedLarge(indexer));
    }

    @Test
    void largeSparseBitsOfAnotherIndexerAreNotPacked() {
        // a hybrid set takes over the bits, with their indexer, of a large set it absorbs
        HybridBitSet<Integer> set = new HybridBitSet<>(indexer, true);
        set.addAllDiff(largeSparseSet(otherIndexer));
        assertNull(set.toPackedLarge(indexer));
    }

    @Test
    void largeSetOfAnotherIndexerIsNotPacked() {
        assertNull(largeSparseSet(otherIndexer).toPackedLarge(indexer));
    }

    private static HybridBitSet<Integer> largeSparseSet(Indexer<Integer> indexer) {
        HybridBitSet<Integer> set = new HybridBitSet<>(indexer, true);
        // more elements than a small set holds, across several areas
        for (int i = 0; i < 40; ++i) {
            set.add(i * 70_001);
        }
        return set;
    }

    private static List<Integer> order(HybridBitSet<Integer> set) {
        return new ArrayList<>(set);
    }
}
