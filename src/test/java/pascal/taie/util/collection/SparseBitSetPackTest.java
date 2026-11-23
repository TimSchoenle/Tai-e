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
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks that {@link SparseBitSet#ofPacked(long[])} restores the set that
 * {@link SparseBitSet#toPacked()} packed, against a sorted set of indexes.
 */
class SparseBitSetPackTest {

    @Test
    void randomSetsSurviveThePackedForm() {
        Random random = new Random(7);
        for (int round = 0; round < 2000; ++round) {
            // ranges from one word to many areas, and indexes near the largest int
            int range = 1 << (1 + random.nextInt(24));
            int base = random.nextInt(8) == 0 ? Integer.MAX_VALUE - range : 0;
            int bits = random.nextInt(200);
            TreeSet<Integer> expected = new TreeSet<>();
            SparseBitSet set = new SparseBitSet();
            for (int i = 0; i < bits; ++i) {
                int index = base + random.nextInt(range);
                expected.add(index);
                set.set(index);
            }
            if (random.nextInt(4) == 0 && bits > 0) {
                // a cleared word leaves a zero word, or a zero block, behind
                int index = expected.pollFirst();
                set.clear(index);
            }
            SparseBitSet restored = SparseBitSet.ofPacked(set.toPacked());
            assertSameBits(expected, restored, "round " + round);
            assertEquals(set, restored, "round " + round);
        }
    }

    @Test
    void packedFormHoldsOnlyNonZeroWords() {
        SparseBitSet set = new SparseBitSet();
        set.set(3);
        set.set(64 * 5 + 1);
        set.set(1 << 20);
        set.set(1 << 20 | 2);
        // two blocks: block 0 with words 0 and 5, the block of bit 2^20 with one word
        assertEquals(5, set.toPacked().length);
        set.clear(1 << 20);
        set.clear(1 << 20 | 2);
        assertEquals(3, set.toPacked().length);
        assertEquals(0, new SparseBitSet().toPacked().length);
        assertTrue(SparseBitSet.ofPacked(new long[0]).isEmpty());
    }

    private static void assertSameBits(TreeSet<Integer> expected, SparseBitSet actual, String at) {
        assertEquals(expected.size(), actual.cardinality(), at);
        int a = actual.nextSetBit(0);
        for (int e : expected) {
            assertEquals(e, a, at);
            a = a == Integer.MAX_VALUE - 1 ? -1 : actual.nextSetBit(a + 1);
        }
        assertEquals(-1, a, at);
    }
}
