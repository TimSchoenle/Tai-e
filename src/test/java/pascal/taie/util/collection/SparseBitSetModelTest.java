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

import java.util.BitSet;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks {@link SparseBitSet} against {@link java.util.BitSet} over random
 * operation sequences: single-bit updates, union, difference, intersection,
 * union-with-difference, containment, intersection tests and iteration in both
 * directions. Indexes are drawn sparse and dense, from small ranges and from
 * ranges that span many blocks and areas, so block and area boundaries are hit.
 */
class SparseBitSetModelTest {

    private static final int SEQUENCES = 400;

    private static final int STEPS = 60;

    private static final int OPERAND_TRIALS = 300;

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** Index ranges: one block, a few blocks, many areas, and a wide sparse range. */
    private static final int[] RANGES = {1 << 9, 1 << 13, 1 << 18, 1 << 24};

    @Test
    void randomSequencesMatchJavaBitSet() {
        Random random = new Random(0x5eedL);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            SparseBitSet[] sparse = {new SparseBitSet(), new SparseBitSet()};
            BitSet[] model = {new BitSet(), new BitSet()};
            for (int step = 0; step < STEPS; step++) {
                int target = random.nextInt(2);
                SparseBitSet s = sparse[target];
                BitSet m = model[target];
                SparseBitSet so = sparse[1 - target];
                BitSet mo = model[1 - target];
                String at = "sequence " + sequence + " step " + step;
                switch (random.nextInt(10)) {
                    case 0, 1, 2 -> {
                        int count = 1 + random.nextInt(40);
                        for (int i = 0; i < count; i++) {
                            int index = nextIndex(random, range);
                            assertEquals(!m.get(index), s.set(index), at + " set " + index);
                            m.set(index);
                        }
                    }
                    case 3 -> {
                        int index = nextIndex(random, range);
                        assertEquals(m.get(index), s.clear(index), at + " clear " + index);
                        m.clear(index);
                    }
                    case 4 -> {
                        BitSet expected = (BitSet) m.clone();
                        expected.or(mo);
                        assertEquals(!expected.equals(m), s.or(so), at + " or");
                        m.or(mo);
                    }
                    case 5 -> {
                        BitSet expectedDiff = (BitSet) mo.clone();
                        expectedDiff.andNot(m);
                        IBitSet diff = s.orDiff(so);
                        assertSameBits(expectedDiff, diff, at + " orDiff diff");
                        m.or(mo);
                    }
                    case 6 -> {
                        BitSet expected = (BitSet) m.clone();
                        expected.andNot(mo);
                        assertEquals(!expected.equals(m), s.andNot(so), at + " andNot");
                        m.andNot(mo);
                    }
                    case 7 -> {
                        BitSet expected = (BitSet) m.clone();
                        expected.and(mo);
                        assertEquals(!expected.equals(m), s.and(so), at + " and");
                        m.and(mo);
                    }
                    case 8 -> {
                        BitSet missing = (BitSet) mo.clone();
                        missing.andNot(m);
                        assertEquals(missing.isEmpty(), s.contains(so), at + " contains");
                        assertEquals(m.intersects(mo), s.intersects(so), at + " intersects");
                    }
                    default -> {
                        SparseBitSet copy = new SparseBitSet();
                        copy.setTo(s);
                        assertSameBits(m, copy, at + " setTo");
                    }
                }
                assertSameBits(m, s, at);
                probe(random, range, m, s, at);
            }
        }
    }

    /**
     * Unions of random sparse and dense operands, each with some bits set and
     * cleared again so that zero words and all-zero blocks are left in place:
     * the result, the return value of {@code or}, the diff of {@code orDiff}
     * and the unchanged operand must match {@link java.util.BitSet}.
     */
    @Test
    void orAndOrDiffOfSparseAndDenseOperandsMatchJavaBitSet() {
        Random random = new Random(0x0bd1ffL);
        for (int trial = 0; trial < OPERAND_TRIALS; trial++) {
            int range = RANGES[trial % RANGES.length];
            BitSet mt = randomOperand(random, range);
            BitSet ms = randomOperand(random, range);
            String at = "trial " + trial;

            SparseBitSet target = fill(random, mt, range);
            SparseBitSet source = fill(random, ms, range);
            BitSet union = (BitSet) mt.clone();
            union.or(ms);
            assertEquals(!union.equals(mt), target.or(source), at + " or");
            assertSameBits(union, target, at + " or result");
            assertSameBits(ms, source, at + " or operand");
            assertFalse(target.or(source), at + " or again");

            SparseBitSet diffTarget = fill(random, mt, range);
            BitSet expectedDiff = (BitSet) ms.clone();
            expectedDiff.andNot(mt);
            IBitSet diff = diffTarget.orDiff(source);
            assertSameBits(expectedDiff, diff, at + " orDiff diff");
            assertSameBits(union, diffTarget, at + " orDiff result");
            assertSameBits(ms, source, at + " orDiff operand");
            assertTrue(diffTarget.orDiff(source).isEmpty(), at + " orDiff again");
            int inDiffBlock = clearBitInBlockOf(union, expectedDiff.nextSetBit(0));
            if (inDiffBlock >= 0) {
                diff.set(inDiffBlock);
                assertSameBits(ms, source, at + " diff shares no block with the operand");
                assertSameBits(union, diffTarget, at + " diff shares no block with the target");
            }

            SparseBitSet copy = new SparseBitSet();
            assertEquals(!ms.isEmpty(), copy.or(source), at + " or into empty");
            assertSameBits(ms, copy, at + " copy");
            int inCopiedBlock = clearBitInBlockOf(ms, ms.nextSetBit(0));
            if (inCopiedBlock >= 0) {
                copy.set(inCopiedBlock);
                assertSameBits(ms, source, at + " copy shares no block");
            }
        }
    }

    /** A target with one low bit and an operand far beyond its table: the target table must grow. */
    @Test
    void orAndOrDiffGrowTheTargetTable() {
        int far = RANGES[RANGES.length - 1] - 1;
        SparseBitSet source = new SparseBitSet();
        source.set(far);
        source.set(far - BLOCK_BITS);
        BitSet expected = new BitSet();
        expected.set(1);
        expected.set(far);
        expected.set(far - BLOCK_BITS);

        SparseBitSet target = new SparseBitSet();
        target.set(1);
        assertTrue(target.or(source));
        assertSameBits(expected, target, "or");

        SparseBitSet diffTarget = new SparseBitSet();
        diffTarget.set(1);
        BitSet expectedDiff = (BitSet) expected.clone();
        expectedDiff.clear(1);
        assertSameBits(expectedDiff, diffTarget.orDiff(source), "orDiff diff");
        assertSameBits(expected, diffTarget, "orDiff result");
    }

    /**
     * Returns a bit that is clear in {@code bits} and lies in the same block as
     * {@code setBit}, or -1 if {@code setBit} is negative or its block is full.
     */
    private static int clearBitInBlockOf(BitSet bits, int setBit) {
        if (setBit < 0) {
            return -1;
        }
        int blockStart = setBit & -BLOCK_BITS;
        int clear = bits.nextClearBit(blockStart);
        return clear < blockStart + BLOCK_BITS ? clear : -1;
    }

    /** A sparse operand (few bits over the range), a dense one (runs of set bits) or an empty one. */
    private static BitSet randomOperand(Random random, int range) {
        BitSet bits = new BitSet();
        switch (random.nextInt(3)) {
            case 0 -> {
                int count = random.nextInt(64);
                for (int i = 0; i < count; i++) {
                    bits.set(nextIndex(random, range));
                }
            }
            case 1 -> {
                int runs = 1 + random.nextInt(8);
                for (int i = 0; i < runs; i++) {
                    int from = random.nextInt(range);
                    int end = Math.min(range, from + random.nextInt(Math.min(range, 1 << 14)));
                    for (int b = from; b < end; b++) {
                        if (random.nextInt(4) != 0) {
                            bits.set(b);
                        }
                    }
                }
            }
            default -> {
                // the empty operand
            }
        }
        return bits;
    }

    /**
     * Builds a sparse bit set holding {@code bits}, after setting and clearing
     * extra bits outside it so that zero words and all-zero blocks remain.
     */
    private static SparseBitSet fill(Random random, BitSet bits, int range) {
        SparseBitSet set = new SparseBitSet();
        int[] extra = new int[random.nextInt(16)];
        for (int i = 0; i < extra.length; i++) {
            extra[i] = nextIndex(random, range);
            set.set(extra[i]);
        }
        for (int b = bits.nextSetBit(0); b >= 0; b = bits.nextSetBit(b + 1)) {
            set.set(b);
        }
        for (int index : extra) {
            if (!bits.get(index)) {
                set.clear(index);
            }
        }
        return set;
    }

    @Test
    void clearOfClearBitInExistingBlockReportsNoChange() {
        SparseBitSet s = new SparseBitSet();
        s.set(0);
        assertFalse(s.clear(1));
        assertTrue(s.clear(0));
        assertFalse(s.clear(0));
    }

    private static int nextIndex(Random random, int range) {
        return switch (random.nextInt(4)) {
            // at or just before a word boundary (some are block or area boundaries)
            case 0 -> Math.max(0, (random.nextInt(range) & -64) - random.nextInt(2));
            default -> random.nextInt(range);
        };
    }

    private static void probe(Random random, int range, BitSet m, SparseBitSet s, String at) {
        for (int i = 0; i < 8; i++) {
            int index = random.nextInt(range + 64);
            assertEquals(m.get(index), s.get(index), at + " get " + index);
            assertEquals(m.nextSetBit(index), s.nextSetBit(index), at + " nextSetBit " + index);
            assertEquals(m.nextClearBit(index), s.nextClearBit(index), at + " nextClearBit " + index);
            assertEquals(m.previousSetBit(index), s.previousSetBit(index), at + " previousSetBit " + index);
            assertEquals(m.previousClearBit(index), s.previousClearBit(index),
                    at + " previousClearBit " + index);
        }
    }

    private static void assertSameBits(BitSet m, IBitSet s, String at) {
        assertEquals(m.cardinality(), s.cardinality(), at + " cardinality");
        assertEquals(m.length(), s.length(), at + " length");
        assertEquals(m.isEmpty(), s.isEmpty(), at + " isEmpty");
        int expected = m.nextSetBit(0);
        int actual = s.nextSetBit(0);
        while (expected >= 0 || actual >= 0) {
            assertEquals(expected, actual, at + " iteration");
            expected = m.nextSetBit(expected + 1);
            actual = s.nextSetBit(actual + 1);
        }
        int last = m.length() - 1;
        if (last >= 0) {
            assertEquals(last, s.previousSetBit(last), at + " last");
        }
    }
}
