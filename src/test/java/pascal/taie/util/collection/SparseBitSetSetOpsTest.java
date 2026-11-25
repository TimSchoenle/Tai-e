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

import java.lang.reflect.Field;
import java.util.BitSet;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link SparseBitSet#minus} gives the set, table and state that a set built
 * bit by bit from the difference has, and the
 * state of a packed set is brought up to date without restoring its blocks.
 */
class SparseBitSetSetOpsTest {

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** The bits of one area of a sparse bit set, from its geometry. */
    private static final int AREA_BITS = 1 << (SparseBitSet.SHIFT1 + SparseBitSet.SHIFT3);

    private static final int PAIRS = 300;

    private static SparseBitSet sparse(BitSet bits, boolean packed) {
        SparseBitSet set = new SparseBitSet();
        for (int i = bits.nextSetBit(0); i >= 0; i = bits.nextSetBit(i + 1)) {
            set.set(i);
        }
        if (packed) {
            set.pack();
        }
        return set;
    }

    /** Random bits over a few areas, at times clustered in a few blocks. */
    private static BitSet randomBits(Random random, int areas) {
        BitSet bits = new BitSet();
        int n = random.nextInt(120);
        int base = random.nextInt(areas * AREA_BITS);
        boolean clustered = random.nextBoolean();
        for (int i = 0; i < n; i++) {
            bits.set(clustered
                    ? base + random.nextInt(4 * BLOCK_BITS)
                    : random.nextInt(areas * AREA_BITS));
        }
        return bits;
    }

    private static Object field(Object owner, String name) throws ReflectiveOperationException {
        Field field = owner.getClass().getDeclaredField(name);
        field.setAccessible(true);
        return field.get(owner);
    }

    private static int tableLength(SparseBitSet set) throws ReflectiveOperationException {
        return ((long[][][]) field(set, "table")).length;
    }

    private static void assertSameState(SparseBitSet expected, SparseBitSet actual, String at) {
        assertEquals(expected.cardinality(), actual.cardinality(), at);
        assertEquals(expected.hashCode(), actual.hashCode(), at);
        assertEquals(expected.length(), actual.length(), at);
        assertEquals(expected.size(), actual.size(), at);
        assertEquals(expected.isEmpty(), actual.isEmpty(), at);
    }

    @Test
    void minusHasTheTableAndStateOfTheDifferenceBuiltBitByBit()
            throws ReflectiveOperationException {
        Random random = new Random(0x45f5L);
        for (int p = 0; p < PAIRS; p++) {
            int areas = 1 + random.nextInt(40);
            BitSet a = randomBits(random, areas);
            BitSet b = random.nextInt(4) == 0 ? (BitSet) a.clone() : randomBits(random, areas);
            if (random.nextBoolean()) {
                // the last areas of a vanish from the difference
                b.or(a.get(a.length() / 2, a.length()));
            }
            BitSet difference = (BitSet) a.clone();
            difference.andNot(b);
            SparseBitSet model = sparse(difference, false);
            for (int forms = 0; forms < 4; forms++) {
                String at = "pair " + p + " forms " + forms;
                SparseBitSet self = sparse(a, (forms & 1) != 0);
                SparseBitSet other = sparse(b, (forms & 2) != 0);
                SparseBitSet minus = self.minus(other);
                assertFalse(minus.isPacked(), at);
                assertEquals(tableLength(model), tableLength(minus), at + ": table");
                assertEquals(field(model, "bitsLength"), field(minus, "bitsLength"), at);
                assertArrayEquals(model.toPacked(), minus.toPacked(), at);
                assertSameState(model, minus, at);
                int bit = random.nextInt((areas + 2) * AREA_BITS);
                SparseBitSet modelCopy = (SparseBitSet) model.copy();
                assertEquals(modelCopy.set(bit), minus.set(bit), at);
                assertSameState(modelCopy, minus, at);
            }
        }
    }

    /**
     * A packed set whose state is out of date answers every state query as
     * the same set with blocks, and stays packed.
     */
    @Test
    void stateOfAPackedSetIsUpdatedInPlace() throws ReflectiveOperationException {
        Random random = new Random(0x5a7eL);
        for (int p = 0; p < PAIRS; p++) {
            String at = "set " + p;
            BitSet bits = randomBits(random, 1 + random.nextInt(40));
            SparseBitSet model = sparse(bits, false);
            SparseBitSet packed = sparse(bits, true);
            assertTrue(packed.isPacked(), at);
            Object state = field(packed, "state");
            Field valid = state.getClass().getDeclaredField("valid");
            valid.setAccessible(true);
            valid.setBoolean(state, false);
            SparseBitSet source = sparse(randomBits(random, 40), random.nextBoolean());
            assertEquals(model.orSummary(source), packed.orSummary(source), at);
            assertTrue(packed.isPacked(), at + ": orSummary restored the blocks");
            assertSameState(model, packed, at);
            assertTrue(packed.isPacked(), at + ": a state query restored the blocks");
            // a copy of a packed set starts from its state and updates it word by word
            SparseBitSet copy = (SparseBitSet) packed.copy();
            SparseBitSet modelCopy = (SparseBitSet) model.copy();
            int bit = random.nextInt(42 * AREA_BITS);
            assertEquals(modelCopy.set(bit), copy.set(bit), at);
            assertSameState(modelCopy, copy, at);
        }
    }
}
