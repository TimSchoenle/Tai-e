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

import org.junit.jupiter.api.Test;
import pascal.taie.util.SimpleIndexer;
import pascal.taie.util.collection.IndexerBitSet;
import pascal.taie.util.collection.SparseBitSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.BLOCKS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.BLOCK_BYTES;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.ENTRIES;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.LARGE;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.OBJECTS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.PACKED;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.PENDING_PACKED;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.SETS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.THROW_RESULT;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.WORDS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.WORD_BYTES;

class HeapOwnerCensusTest {

    /**
     * Bits 1 and 70 lie in words 0 and 1 of block 0, bit 5000 in word 78,
     * which is in another block for any block of at most 64 words.
     */
    private static SparseBitSet threeWordsInTwoBlocks() {
        SparseBitSet bits = new SparseBitSet();
        bits.set(1);
        bits.set(70);
        bits.set(5000);
        return bits;
    }

    @Test
    void shapeOfAnUnpackedAndOfAPackedSet() {
        SparseBitSet bits = threeWordsInTwoBlocks();
        long[] shape = new long[SparseBitSet.SHAPE_LENGTH];
        bits.addShape(shape);
        assertEquals(2, shape[SparseBitSet.SHAPE_BLOCKS]);
        assertEquals(3, shape[SparseBitSet.SHAPE_WORDS]);
        assertEquals(0, shape[SparseBitSet.SHAPE_PACKED_WORDS]);
        assertEquals(true, shape[SparseBitSet.SHAPE_AREAS] >= 1);
        assertEquals(true, shape[SparseBitSet.SHAPE_TABLE] >= shape[SparseBitSet.SHAPE_AREAS]);
        int packedLength = bits.toPacked().length;
        bits.pack();
        long[] packed = new long[SparseBitSet.SHAPE_LENGTH];
        bits.addShape(packed);
        assertEquals(2, packed[SparseBitSet.SHAPE_BLOCKS]);
        assertEquals(3, packed[SparseBitSet.SHAPE_WORDS]);
        assertEquals(packedLength, packed[SparseBitSet.SHAPE_PACKED_WORDS]);
        assertEquals(0, packed[SparseBitSet.SHAPE_TABLE]);
    }

    @Test
    void areasAreChargedAtTheirOwnLength() {
        SparseBitSet one = new SparseBitSet();
        one.set(1);
        long[] shape = new long[SparseBitSet.SHAPE_LENGTH];
        one.addShape(shape);
        assertEquals(1, shape[SparseBitSet.SHAPE_AREAS]);
        assertEquals(1, shape[SparseBitSet.SHAPE_AREA_SLOTS]);
        assertEquals(1, shape[SparseBitSet.SHAPE_ONE_SLOT_AREAS]);
        long[] noArea = shape.clone();
        noArea[SparseBitSet.SHAPE_AREAS] = 0;
        noArea[SparseBitSet.SHAPE_AREA_SLOTS] = 0;
        noArea[SparseBitSet.SHAPE_ONE_SLOT_AREAS] = 0;
        long base = PointsToSetCensus.bitSetBytes(noArea, true, false);
        // 16 B header plus one 4 B slot, aligned to 8
        assertEquals(base + 24, PointsToSetCensus.bitSetBytes(shape, true, false));
        long[] full = noArea.clone();
        full[SparseBitSet.SHAPE_AREAS] = 1;
        full[SparseBitSet.SHAPE_AREA_SLOTS] = SparseBitSet.BLOCKS_PER_AREA;
        assertEquals(base + 16 + 4L * SparseBitSet.BLOCKS_PER_AREA,
                PointsToSetCensus.bitSetBytes(full, true, false));
        long[] two = new long[SparseBitSet.SHAPE_LENGTH];
        threeWordsInTwoBlocks().addShape(two);
        assertEquals(0, two[SparseBitSet.SHAPE_ONE_SLOT_AREAS]);
        assertEquals(true, two[SparseBitSet.SHAPE_AREA_SLOTS] < SparseBitSet.BLOCKS_PER_AREA);
    }

    @Test
    void packedPendingDeltaCountsItsHeadersWordsAndObjectsOnce() {
        long[] packed = threeWordsInTwoBlocks().toPacked();
        HeapOwnerCensus census = new HeapOwnerCensus();
        census.addPending(packed);
        census.addPending(packed);
        assertEquals(2, census.get(PENDING_PACKED, ENTRIES));
        assertEquals(1, census.get(PENDING_PACKED, SETS));
        assertEquals(3, census.get(PENDING_PACKED, OBJECTS));
        assertEquals(1, census.get(PENDING_PACKED, PACKED));
        assertEquals(2, census.get(PENDING_PACKED, BLOCKS));
        assertEquals(3, census.get(PENDING_PACKED, WORDS));
        assertEquals(24, census.get(PENDING_PACKED, WORD_BYTES));
        assertEquals(16 + 8 * 5, census.get(PENDING_PACKED, BLOCK_BYTES));
    }

    @Test
    void pendingSnapshotCountsAsItsPackedWords() {
        SparseBitSet bits = threeWordsInTwoBlocks();
        long[] packed = bits.toPacked();
        HeapOwnerCensus words = new HeapOwnerCensus();
        words.addPending(packed);
        bits.pack();
        SparseBitSet.PackedSnapshot snapshot = bits.packedSnapshot();
        assertEquals(true, snapshot != null);
        HeapOwnerCensus snapshots = new HeapOwnerCensus();
        snapshots.addPending(snapshot);
        snapshots.addPending(snapshot);
        assertEquals(2, snapshots.get(PENDING_PACKED, ENTRIES));
        for (int column = SETS; column < HeapOwnerCensus.COLUMNS; ++column) {
            assertEquals(words.get(PENDING_PACKED, column),
                    snapshots.get(PENDING_PACKED, column), "column " + column);
        }
    }

    @Test
    void throwSetCountsItsBits() {
        IndexerBitSet<String> set = new IndexerBitSet<>(new SimpleIndexer<>(), true);
        set.add("a");
        set.add("b");
        HeapOwnerCensus census = new HeapOwnerCensus();
        census.addThrowSet(set);
        assertEquals(1, census.get(THROW_RESULT, SETS));
        assertEquals(2, census.get(THROW_RESULT, OBJECTS));
        assertEquals(1, census.get(THROW_RESULT, LARGE));
        assertEquals(1, census.get(THROW_RESULT, BLOCKS));
        assertEquals(1, census.get(THROW_RESULT, WORDS));
        assertEquals(0, census.get(THROW_RESULT, PACKED));
        // one level3 block: an array header and its words, 8-byte aligned
        long block = (16 + 8L * SparseBitSet.WORDS_PER_BLOCK + 7) & ~7L;
        assertEquals(block, census.get(THROW_RESULT, BLOCK_BYTES));
        assertEquals(8, census.get(THROW_RESULT, WORD_BYTES));
    }
}
