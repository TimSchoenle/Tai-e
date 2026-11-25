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

import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Checks {@link SparseBitSet#orSummary} and {@link SparseBitSet#minus}
 * against {@code or} and {@code andNot} on copies, for sets whose state is
 * up to date, out of date, or left by a recompute that removed all-zero
 * blocks.
 */
class SparseBitSetUnionSummaryTest {

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** Index ranges: one block, a few blocks, many blocks and areas. */
    private static final int[] RANGES = {BLOCK_BITS, 4 * BLOCK_BITS, 1 << 18, 1 << 22};

    @Test
    void summaryAndDifferenceMatchTheChangedCopy() {
        Random random = new Random(0x5a33L);
        for (int sequence = 0; sequence < 400; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            SparseBitSet self = randomSet(random, range);
            SparseBitSet source = randomSet(random, range);
            if (random.nextBoolean()) {
                // a recompute that removes all-zero blocks
                self.andNot(randomSet(random, range));
                self.hashCode();
            }
            SparseBitSet selfBefore = (SparseBitSet) self.copy();
            SparseBitSet sourceBefore = (SparseBitSet) source.copy();
            String at = "sequence " + sequence;

            long summary = self.orSummary(source);
            SparseBitSet union = rebuilt(self, source);
            assertEquals(union.hashCode(), SparseBitSet.unionHash(summary), at + " hash");
            assertEquals(union.cardinality(), SparseBitSet.unionCardinality(summary),
                    at + " cardinality");

            SparseBitSet added = source.minus(self);
            SparseBitSet expected = (SparseBitSet) source.copy();
            expected.andNot(self);
            assertEquals(expected, added, at + " difference");
            assertEquals(expected.hashCode(), added.hashCode(), at + " difference hash");

            assertEquals(selfBefore, self, at + " self changed");
            assertEquals(sourceBefore, source, at + " source changed");
        }
    }

    /**
     * {@link SparseBitSet#setSummary} against a fresh set rebuilt with the
     * bits, for table and packed sets and bit lists with repeats, bits the
     * set holds, several new bits in one word and bits far apart.
     */
    @Test
    void setSummaryMatchesTheSetRebuiltWithTheBits() {
        Random random = new Random(0x5e75L);
        for (int sequence = 0; sequence < 800; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            SparseBitSet self = randomSet(random, range);
            boolean packed = sequence % 3 == 0;
            if (packed) {
                self.pack();
            } else if (random.nextBoolean()) {
                self.andNot(randomSet(random, range));
                self.hashCode();
            }
            int[] bits = new int[random.nextInt(9)];
            for (int i = 0; i < bits.length; i++) {
                int kind = random.nextInt(4);
                int held = self.nextSetBit(random.nextInt(range));
                if (kind == 0 && i > 0) {
                    bits[i] = bits[random.nextInt(i)];
                } else if (kind == 1 && held >= 0) {
                    bits[i] = held;
                } else if (kind == 2 && i > 0) {
                    // another bit of the word of an earlier bit
                    int word = bits[random.nextInt(i)] & -Long.SIZE;
                    bits[i] = word + random.nextInt(Long.SIZE);
                } else {
                    bits[i] = random.nextInt(range);
                }
            }
            SparseBitSet selfBefore = (SparseBitSet) self.copy();
            String at = "sequence " + sequence;

            long summary = self.setSummary(bits);
            SparseBitSet expected = rebuilt(self, new SparseBitSet());
            for (int bit : bits) {
                expected.set(bit);
            }
            assertEquals(expected.hashCode(), SparseBitSet.unionHash(summary), at + " hash");
            assertEquals(expected.cardinality(), SparseBitSet.unionCardinality(summary),
                    at + " cardinality");
            assertEquals(selfBefore, self, at + " self changed");
            assertEquals(packed, self.isPacked(), at + " packed form changed");
        }
    }

    @Test
    void setSummaryRefusesTheBitsThatSetRefuses() {
        SparseBitSet set = randomSet(new Random(11), BLOCK_BITS);
        assertThrows(IndexOutOfBoundsException.class, () -> set.setSummary(new int[]{1, -1}));
        assertThrows(IndexOutOfBoundsException.class, () -> set.set(Integer.MAX_VALUE));
        assertThrows(IndexOutOfBoundsException.class,
                () -> set.setSummary(new int[]{Integer.MAX_VALUE}));
        long empty = set.setSummary(new int[0]);
        assertEquals(set.hashCode(), SparseBitSet.unionHash(empty));
        assertEquals(set.cardinality(), SparseBitSet.unionCardinality(empty));
    }

    @Test
    void summaryOfASetWithItselfIsItsOwnState() {
        SparseBitSet set = randomSet(new Random(7), 1 << 18);
        long summary = set.orSummary(set);
        assertEquals(set.hashCode(), SparseBitSet.unionHash(summary));
        assertEquals(set.cardinality(), SparseBitSet.unionCardinality(summary));
        assertEquals(new SparseBitSet(), set.minus(set));
    }

    /**
     * The union of both sets in a fresh set built bit by bit, whose state
     * is computed on its first read, not updated word by word as the
     * summary is.
     */
    private static SparseBitSet rebuilt(SparseBitSet a, SparseBitSet b) {
        SparseBitSet union = new SparseBitSet();
        for (SparseBitSet s : new SparseBitSet[]{a, b}) {
            for (int i = s.nextSetBit(0); i >= 0; i = s.nextSetBit(i + 1)) {
                union.set(i);
            }
        }
        return union;
    }

    private static SparseBitSet randomSet(Random random, int range) {
        SparseBitSet set = new SparseBitSet();
        int count = random.nextInt(40);
        for (int i = 0; i < count; i++) {
            set.set(random.nextInt(range));
        }
        return set;
    }
}
