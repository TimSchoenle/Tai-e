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

import java.util.Arrays;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link SparseBitSet#packedContains}: on the words of
 * {@link SparseBitSet#toPacked()} and on a snapshot of a packed set, for a
 * tested set in blocks or packed and for single bits, the answer is that of
 * {@link SparseBitSet#contains} on the set, and the words are not written.
 */
class SparseBitSetPackedContainsTest {

    @Test
    void packedContainsAnswersAsContains() {
        int contained = 0;
        int notContained = 0;
        for (int seed = 0; seed < 2000; ++seed) {
            Random random = new Random(seed);
            SparseBitSet self = randomSet(random);
            SparseBitSet other = random.nextInt(3) == 0 ? subset(self, random) : randomSet(random);
            if (random.nextInt(3) == 0) {
                // a bit of a present word, of a missing word of a present block, or past the last block
                int bit = random.nextInt(3) == 0 ? (1 << 20) + random.nextInt(1 << 10)
                        : random.nextInt(1 << 12);
                other.set(bit);
            }
            boolean expected = self.contains(other);
            if (expected) {
                ++contained;
            } else {
                ++notContained;
            }
            long[] words = self.toPacked();
            long[] wordsBefore = words.clone();
            SparseBitSet stored = self.copy();
            stored.pack();
            SparseBitSet.PackedSnapshot snapshot = stored.packedSnapshot();
            assertTrue(snapshot != null);
            int[] bits = bits(other);
            for (boolean otherPacked : new boolean[]{false, true}) {
                SparseBitSet tested = other.copy();
                if (otherPacked) {
                    tested.pack();
                }
                assertEquals(expected, SparseBitSet.packedContains(words, tested), "seed " + seed);
                assertEquals(expected, SparseBitSet.packedContains(snapshot, tested), "seed " + seed);
            }
            int[] shuffled = shuffle(bits, random);
            assertEquals(expected, SparseBitSet.packedContains(words, shuffled.clone()), "seed " + seed);
            assertEquals(expected, SparseBitSet.packedContains(snapshot, shuffled), "seed " + seed);
            assertArrayEquals(wordsBefore, words, "seed " + seed);
            assertEquals(self, SparseBitSet.ofSnapshot(snapshot), "seed " + seed);
        }
        assertTrue(contained > 300, "contained: " + contained);
        assertTrue(notContained > 300, "not contained: " + notContained);
        // empty on either side
        SparseBitSet empty = new SparseBitSet();
        SparseBitSet one = new SparseBitSet();
        one.set(70);
        assertTrue(SparseBitSet.packedContains(one.toPacked(), empty));
        assertTrue(SparseBitSet.packedContains(empty.toPacked(), new int[0]));
        assertEquals(false, SparseBitSet.packedContains(empty.toPacked(), one));
        assertEquals(false, SparseBitSet.packedContains(empty.toPacked(), new int[]{70}));
    }

    /**
     * Bits in few blocks, several per word, some blocks far apart.
     */
    private static SparseBitSet randomSet(Random random) {
        SparseBitSet set = new SparseBitSet();
        int n = random.nextInt(40);
        for (int i = 0; i < n; ++i) {
            int base = random.nextInt(4) == 0 ? random.nextInt(1 << 20) : 0;
            set.set(base + random.nextInt(1 << 12));
        }
        return set;
    }

    private static SparseBitSet subset(SparseBitSet set, Random random) {
        SparseBitSet subset = new SparseBitSet();
        for (int bit : bits(set)) {
            if (random.nextBoolean()) {
                subset.set(bit);
            }
        }
        return subset;
    }

    private static int[] bits(SparseBitSet set) {
        int[] bits = new int[set.cardinality()];
        int i = 0;
        for (int bit = set.nextSetBit(0); bit >= 0; bit = set.nextSetBit(bit + 1)) {
            bits[i++] = bit;
        }
        return bits;
    }

    private static int[] shuffle(int[] bits, Random random) {
        int[] shuffled = Arrays.copyOf(bits, bits.length);
        for (int i = shuffled.length - 1; i > 0; --i) {
            int j = random.nextInt(i + 1);
            int t = shuffled[i];
            shuffled[i] = shuffled[j];
            shuffled[j] = t;
        }
        return shuffled;
    }
}
