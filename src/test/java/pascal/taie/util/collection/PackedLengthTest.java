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

import java.lang.management.ManagementFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link SparseBitSet#packedLength()} is the length of
 * {@link SparseBitSet#toPacked()}, and {@link GenericBitSet#packedBytes()}
 * estimates it without copying the words.
 */
class PackedLengthTest {

    private static final int SPREAD = 4096;

    private static final int STEP = 97;

    @Test
    void packedLengthIsTheLengthOfThePackedWords() {
        SparseBitSet set = new SparseBitSet();
        assertEquals(set.toPacked().length, set.packedLength());
        for (int i = 0; i < SPREAD; ++i) {
            set.set(i * STEP);
        }
        // an all-zero block the packed form leaves out
        set.set(SPREAD * STEP + 1);
        set.clear(SPREAD * STEP + 1);
        int unpacked = set.toPacked().length;
        assertEquals(unpacked, set.packedLength());
        set.pack();
        assertTrue(set.isPacked());
        assertEquals(set.toPacked().length, set.packedLength());
        assertEquals(unpacked, set.packedLength());
    }

    @Test
    void packedBytesCopiesNoWords() {
        Indexer<Integer> indexer = new Indexer<>() {
            @Override
            public int getIndex(Integer o) {
                return o;
            }

            @Override
            public Integer getObject(int index) {
                return index;
            }
        };
        IndexerBitSet<Integer> bits = new IndexerBitSet<>(indexer, true);
        for (int i = 0; i < SPREAD; ++i) {
            bits.add(i * STEP);
        }
        com.sun.management.ThreadMXBean threads =
                (com.sun.management.ThreadMXBean) ManagementFactory.getThreadMXBean();
        long thread = Thread.currentThread().getId();
        long expected = bits.packedBytes();
        long before = threads.getThreadAllocatedBytes(thread);
        long bytes = bits.packedBytes();
        long allocated = threads.getThreadAllocatedBytes(thread) - before;
        assertEquals(expected, bytes);
        // the packed copy would take more than 8 bytes for each of the
        // SPREAD words
        assertTrue(allocated < SPREAD, "packedBytes allocated " + allocated + " bytes");
    }
}
