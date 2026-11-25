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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A packed set answers every query as the same set with blocks: each test
 * builds the same random set twice, packs one of them and compares it with
 * the other (the model).
 */
class SparseBitSetPackedTest {

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** Index ranges: one block, a few blocks, many blocks and areas. */
    private static final int[] RANGES = {BLOCK_BITS, 4 * BLOCK_BITS, 1 << 18, 1 << 22};

    private static final int SEQUENCES = 400;

    /**
     * A random set: scattered or clustered bits, at times with a cleared
     * bit (which can leave an all-zero word or block) and an out-of-date
     * state.
     */
    private static SparseBitSet randomSet(Random random, int range) {
        SparseBitSet set = new SparseBitSet();
        int n = random.nextInt(80);
        boolean clustered = random.nextBoolean();
        int base = random.nextInt(range);
        int last = -1;
        for (int i = 0; i < n; i++) {
            last = clustered
                    ? Math.min(range - 1, base + random.nextInt(2 * BLOCK_BITS))
                    : random.nextInt(range);
            set.set(last);
        }
        if (random.nextInt(6) == 0) {
            // one bit per word over many words: ranks beyond the low header bits
            int start = random.nextInt(range);
            for (int word = start >> 6; word < Math.min(range >> 6, (start >> 6) + 700); word++) {
                set.set((word << 6) + random.nextInt(64));
            }
        }
        if (last >= 0 && random.nextInt(3) == 0) {
            set.clear(last);
        }
        if (random.nextBoolean()) {
            set.hashCode();
        }
        return set;
    }

    private static List<Integer> bits(SparseBitSet set) {
        List<Integer> bits = new ArrayList<>();
        for (int i = set.nextSetBit(0); i >= 0; i = set.nextSetBit(i + 1)) {
            bits.add(i);
        }
        return bits;
    }

    private static void assertSameState(SparseBitSet expected, SparseBitSet actual, String at) {
        assertEquals(expected.cardinality(), actual.cardinality(), at);
        assertEquals(expected.hashCode(), actual.hashCode(), at);
        assertEquals(expected.length(), actual.length(), at);
        assertEquals(expected.size(), actual.size(), at);
        assertEquals(expected.isEmpty(), actual.isEmpty(), at);
    }

    @Test
    void readsOfAPackedSetMatchTheModelAndKeepItPacked() {
        Random random = new Random(0x9ac4L);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            long seed = random.nextLong();
            SparseBitSet model = randomSet(new Random(seed), range);
            SparseBitSet packed = randomSet(new Random(seed), range);
            // pack() brings the state up to date first
            model.hashCode();
            packed.pack();
            String at = "sequence " + sequence;
            assertTrue(packed.isPacked(), at);

            assertSameState(model, packed, at);
            List<Integer> bits = bits(model);
            assertEquals(bits, bits(packed), at);
            assertArrayEquals(model.toPacked(), packed.toPacked(), at);
            for (int k = 0; k < 64; k++) {
                int from = random.nextInt(range + 2 * BLOCK_BITS);
                assertEquals(model.nextSetBit(from), packed.nextSetBit(from), at + " from " + from);
                assertEquals(model.get(from), packed.get(from), at + " get " + from);
            }
            for (int bit : bits) {
                assertTrue(packed.get(bit), at);
                assertEquals(model.get(bit + 1), packed.get(bit + 1), at);
                assertEquals(model.nextSetBit(bit), packed.nextSetBit(bit), at);
                assertEquals(model.nextSetBit(bit + 1), packed.nextSetBit(bit + 1), at);
            }
            assertEquals(model.nextSetBit(Integer.MAX_VALUE),
                    packed.nextSetBit(Integer.MAX_VALUE), at);

            SparseBitSet other = randomSet(random, range);
            SparseBitSet packedOther = (SparseBitSet) other.copy();
            packedOther.pack();
            SparseBitSet subset = (SparseBitSet) model.copy();
            subset.andNot(randomSet(random, range));
            assertEquals(model.contains(other), packed.contains(other), at);
            assertEquals(model.contains(other), packed.contains(packedOther), at);
            assertEquals(other.contains(model), other.contains(packed), at);
            assertEquals(other.contains(model), packedOther.contains(packed), at);
            assertTrue(packed.contains(subset), at);
            assertTrue(packed.contains(model) && model.contains(packed), at);
            assertTrue(packed.equals(model) && model.equals(packed), at);
            assertEquals(model.equals(other), packed.equals(packedOther), at);

            assertEquals(model.orSummary(other), packed.orSummary(other), at);
            assertEquals(model.orSummary(other), packed.orSummary(packedOther), at);
            assertEquals(model.orSummary(other), model.orSummary(packedOther), at);
            assertEquals(other.orSummary(model), other.orSummary(packed), at);
            assertArrayEquals(other.minus(model).toPacked(), other.minus(packed).toPacked(), at);
            assertArrayEquals(model.minus(other).toPacked(), packed.minus(other).toPacked(), at);
            assertArrayEquals(model.minus(other).toPacked(),
                    packed.minus(packedOther).toPacked(), at);

            SparseBitSet copy = (SparseBitSet) packed.copy();
            SparseBitSet modelCopy = (SparseBitSet) model.copy();
            assertFalse(copy.isPacked(), at);
            assertSameState(modelCopy, copy, at);
            assertEquals(bits, bits(copy), at);
            int bit = random.nextInt(range);
            assertEquals(modelCopy.set(bit), copy.set(bit), at);
            assertSameState(modelCopy, copy, at);
            assertEquals(bits(modelCopy), bits(copy), at);

            assertTrue(packed.isPacked(), at + ": a read restored the blocks");
            assertTrue(packedOther.isPacked(), at + ": a read restored the blocks");
            assertEquals(bits, bits(packed), at + ": a copy changed the packed set");
        }
    }

    /**
     * The two reads of a type filter, {@link SparseBitSet#updateMemoAndCount}
     * and {@link SparseBitSet#forEachAnd}, on a packed set: the same tests in
     * the same order, the same memo sets, count and visited bits as the
     * model, and the packed set stays packed.
     */
    @Test
    void filterReadsOfAPackedSetMatchTheModelAndKeepItPacked() {
        Random random = new Random(0x7e1fL);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            long seed = random.nextLong();
            SparseBitSet model = randomSet(new Random(seed), range);
            SparseBitSet packed = randomSet(new Random(seed), range);
            model.hashCode();
            packed.pack();
            String at = "sequence " + sequence;

            // memo sets that already know some of the bits, built twice the
            // same way (a copy can drop all-zero blocks, which the state counts)
            long memoSeed = random.nextLong();
            SparseBitSet modelKnown = randomSet(new Random(memoSeed), range);
            SparseBitSet modelPass = randomSet(new Random(memoSeed), range);
            modelPass.andNot(randomSet(new Random(memoSeed + 1), range));
            SparseBitSet known = randomSet(new Random(memoSeed), range);
            SparseBitSet pass = randomSet(new Random(memoSeed), range);
            pass.andNot(randomSet(new Random(memoSeed + 1), range));
            int salt = random.nextInt();
            List<Integer> modelTests = new ArrayList<>();
            List<Integer> tests = new ArrayList<>();
            int modelCount = model.updateMemoAndCount(modelKnown, modelPass,
                    i -> modelTests.add(i) && Integer.bitCount(i ^ salt) % 3 != 0);
            int count = packed.updateMemoAndCount(known, pass,
                    i -> tests.add(i) && Integer.bitCount(i ^ salt) % 3 != 0);
            assertEquals(modelCount, count, at);
            assertEquals(modelTests, tests, at);
            assertEquals(bits(modelKnown), bits(known), at);
            assertEquals(bits(modelPass), bits(pass), at);
            assertSameState(modelKnown, known, at);
            assertSameState(modelPass, pass, at);
            assertTrue(packed.isPacked(), at + ": updateMemoAndCount restored the blocks");

            SparseBitSet other = randomSet(random, range);
            SparseBitSet packedOther = (SparseBitSet) other.copy();
            packedOther.pack();
            List<Integer> want = new ArrayList<>();
            model.forEachAnd(other, want::add);
            List<Integer> got = new ArrayList<>();
            packed.forEachAnd(other, got::add);
            assertEquals(want, got, at);
            got.clear();
            packed.forEachAnd(packedOther, got::add);
            assertEquals(want, got, at);
            got.clear();
            other.forEachAnd(packed, got::add);
            assertEquals(want, got, at);
            got.clear();
            packedOther.forEachAnd(model, got::add);
            assertEquals(want, got, at);
            got.clear();
            packed.forEachAnd(packed, got::add);
            assertEquals(bits(model), got, at);
            assertTrue(packed.isPacked(), at + ": forEachAnd restored the blocks");
            assertTrue(packedOther.isPacked(), at + ": forEachAnd restored the blocks");
            assertEquals(bits(model), bits(packed), at);
        }
    }

    /**
     * {@link SparseBitSet#intersection} of packed and unpacked sets, in both
     * orders: the same bits and state as a copy of the set and then
     * {@link SparseBitSet#and} on the copy, also after one more change; the
     * result is not packed and neither operand changes or is unpacked.
     */
    @Test
    void intersectionMatchesCopyAndAnd() {
        Random random = new Random(0x1a7dL);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            long seed = random.nextLong();
            long otherSeed = random.nextLong();
            SparseBitSet model = randomSet(new Random(seed), range);
            SparseBitSet otherModel = randomSet(new Random(otherSeed), range);
            // at times the set is a subset of the other set: every one of
            // its blocks is shared
            boolean subset = random.nextInt(4) == 0;
            if (subset) {
                otherModel.or(model);
            }
            String at = "sequence " + sequence;
            for (int form = 0; form < 4; ++form) {
                SparseBitSet set = randomSet(new Random(seed), range);
                SparseBitSet other = randomSet(new Random(otherSeed), range);
                if (subset) {
                    other.or(set);
                }
                if ((form & 1) != 0) {
                    set.pack();
                }
                if ((form & 2) != 0) {
                    other.pack();
                }
                String atForm = at + " form " + form;
                SparseBitSet expected = (SparseBitSet) model.copy();
                expected.and(otherModel);
                SparseBitSet got = set.intersection(other);
                assertFalse(got.isPacked(), atForm);
                assertEquals(bits(expected), bits(got), atForm);
                assertSameState(expected, got, atForm);
                assertEquals(bits(model), bits(set), atForm + ": the set changed");
                assertEquals(bits(otherModel), bits(other), atForm + ": the other set changed");
                assertEquals((form & 1) != 0, set.isPacked(), atForm);
                assertEquals((form & 2) != 0, other.isPacked(), atForm);
                int bit = random.nextInt(range);
                assertEquals(expected.set(bit), got.set(bit), atForm);
                assertSameState(expected, got, atForm);
                assertEquals(bits(expected), bits(got), atForm);
            }
        }
    }

    @Test
    void changesOfAPackedSetMatchTheModel() {
        Random random = new Random(0x51d2L);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            long seed = random.nextLong();
            SparseBitSet model = randomSet(new Random(seed), range);
            SparseBitSet packed = randomSet(new Random(seed), range);
            // pack() brings the state up to date first
            model.hashCode();
            packed.pack();
            String at = "sequence " + sequence + " op " + sequence % 7;
            SparseBitSet operand = randomSet(random, range);
            int bit = random.nextInt(range);
            switch (sequence % 7) {
                case 0 -> assertEquals(model.set(bit), packed.set(bit), at);
                case 1 -> assertEquals(model.clear(bit), packed.clear(bit), at);
                case 2 -> assertEquals(model.or(operand), packed.or(operand), at);
                case 3 -> assertArrayEquals(((SparseBitSet) model.orDiff(operand)).toPacked(),
                        ((SparseBitSet) packed.orDiff(operand)).toPacked(), at);
                case 4 -> assertEquals(model.andNot(operand), packed.andNot(operand), at);
                case 5 -> assertEquals(model.and(operand), packed.and(operand), at);
                default -> {
                    assertEquals(model.previousSetBit(bit), packed.previousSetBit(bit), at);
                    assertEquals(model.nextClearBit(bit), packed.nextClearBit(bit), at);
                    assertArrayEquals(model.minus(operand).toPacked(),
                            packed.minus(operand).toPacked(), at);
                }
            }
            // a clear beyond the capacity of the set reads nothing and stays packed
            if (sequence % 7 != 1) {
                assertFalse(packed.isPacked(), at);
            }
            assertSameState(model, packed, at);
            assertEquals(bits(model), bits(packed), at);
            // a packed set as the operand of a change
            long targetSeed = random.nextLong();
            SparseBitSet target = randomSet(new Random(targetSeed), range);
            SparseBitSet modelTarget = randomSet(new Random(targetSeed), range);
            packed.pack();
            assertEquals(modelTarget.or(model), target.or(packed), at);
            assertSameState(modelTarget, target, at);
            assertEquals(bits(modelTarget), bits(target), at);
            SparseBitSet modelDiff = (SparseBitSet) modelTarget.orDiff(operand);
            SparseBitSet packedOperand = (SparseBitSet) operand.copy();
            packedOperand.pack();
            SparseBitSet diff = (SparseBitSet) target.orDiff(packedOperand);
            assertArrayEquals(modelDiff.toPacked(), diff.toPacked(), at);
            assertEquals(modelDiff.hashCode(), diff.hashCode(), at);
            assertSameState(modelTarget, target, at);
            assertTrue(packed.isPacked() && packedOperand.isPacked(),
                    at + ": a union read its packed operand by restoring its blocks");
            packed.pack();
            packed.pack();
            assertEquals(bits(model), bits(packed), at);
        }
    }
}
