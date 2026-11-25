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
import pascal.taie.util.collection.SparseBitSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class PointsToSetCensusTest {

    @Test
    void countsBlocksWordsAndAreasOfOneSet() {
        PointsToSetCensus.Population p = new PointsToSetCensus.Population();
        // block 0: words 0 (bits 0, 1, 63), 1 (bit 64) and 7 (bit 511);
        // block 1: word 8 (bit 512); block 9: word 78 (bit 5000);
        // block 128 (area 1): word 1024 (bit 65536)
        int[] sorted = {0, 1, 63, 64, 511, 512, 5000, 65536};
        PointsToSetCensus.Population.Shape shape = p.record(sorted, sorted.length);
        // area 0 ends at block 9: 16 slots, 16 + 4 * 16 = 80 bytes;
        // area 1 ends at its block 0: 1 slot, 16 + 4 aligned to 24 bytes
        assertEquals(new PointsToSetCensus.Population.Shape(4, 6, 2, 2, 80 + 24), shape);
        SparseBitSet bits = new SparseBitSet();
        for (int i : sorted) {
            bits.set(i);
        }
        assertEquals(bits.toPacked().length, shape.packedLength());
        assertEquals(1, p.sets());
        assertEquals(8, p.objects());
        assertEquals(4, p.blocks());
        assertEquals(6, p.words());
        assertEquals(1, p.cardinality()[4]); // 8 in [8, 15]
        assertEquals(1, p.wordsPerBlock()[3]);
        assertEquals(3, p.wordsPerBlock()[1]);
        assertEquals(1, p.blocksPerSet()[3]); // 4 in [4, 7]
        assertEquals("sets=1 objects=8 blocks=4 words=6 cardinality={[8,15]=1}"
                + " words-per-block={1=3, 2=0, 3=1, 4=0, 5=0, 6=0, 7=0, 8=0}"
                + " blocks-per-set={[4,7]=1}", p.toString());
    }

    @Test
    void emptySetIsCardinalityZeroWithoutBlocks() {
        PointsToSetCensus.Population p = new PointsToSetCensus.Population();
        assertEquals(new PointsToSetCensus.Population.Shape(0, 0, 0, 0, 0),
                p.record(new int[0], 0));
        assertEquals(1, p.cardinality()[0]);
        assertEquals(1, p.blocksPerSet()[0]);
        assertEquals(0, p.blocks());
    }

    @Test
    void fullBlockHasEightWords() {
        PointsToSetCensus.Population p = new PointsToSetCensus.Population();
        int[] sorted = new int[PointsToSetCensus.WORDS_PER_BLOCK];
        for (int w = 0; w < sorted.length; w++) {
            sorted[w] = w * Long.SIZE + 5;
        }
        p.record(sorted, sorted.length);
        assertEquals(1, p.wordsPerBlock()[PointsToSetCensus.WORDS_PER_BLOCK]);
        assertEquals(1, p.blocks());
    }

    @Test
    void bucketsAreLog2() {
        assertEquals(0, PointsToSetCensus.bucket(0));
        assertEquals(1, PointsToSetCensus.bucket(1));
        assertEquals(2, PointsToSetCensus.bucket(2));
        assertEquals(2, PointsToSetCensus.bucket(3));
        assertEquals(3, PointsToSetCensus.bucket(4));
        assertEquals(63, PointsToSetCensus.bucket(Long.MAX_VALUE));
        long[] h = new long[PointsToSetCensus.BUCKETS];
        h[0] = 1;
        h[1] = 2;
        h[63] = 3;
        assertEquals("{[0,0]=1, [1,1]=2, [4611686018427387904,9223372036854775807]=3}",
                PointsToSetCensus.formatHistogram(h));
    }
}
