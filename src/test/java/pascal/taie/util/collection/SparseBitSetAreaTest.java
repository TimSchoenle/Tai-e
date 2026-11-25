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
import pascal.taie.util.SerializationUtils;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks the areas of {@link SparseBitSet}: an area array holds the blocks
 * up to its highest present one, at a power-of-two length, whichever writer
 * created or grew it; and sets built on such areas hold the same bits, in
 * the same order and with the same packed form as {@link java.util.BitSet}
 * says, over random operation sequences that grow, shrink, pack and unpack
 * areas.
 */
class SparseBitSetAreaTest {

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** The bits one area spans. */
    private static final int AREA_BITS = BLOCK_BITS * SparseBitSet.BLOCKS_PER_AREA;

    private static final int WORDS_PER_BLOCK = SparseBitSet.WORDS_PER_BLOCK;

    private static final Field TABLE = tableField();

    @Test
    void anAreaHoldsTheBlocksUpToItsHighestOne() {
        for (int w2 = 0; w2 < SparseBitSet.BLOCKS_PER_AREA; ++w2) {
            SparseBitSet set = new SparseBitSet();
            // in the second area, so that the first stays absent
            set.set(AREA_BITS + w2 * BLOCK_BITS + 5);
            long[][][] table = table(set);
            assertNull(table[0], "block " + w2);
            assertEquals(tightLength(w2), table[1].length, "block " + w2);
        }
    }

    @Test
    void areasGrowAsHigherBlocksArrive() {
        SparseBitSet set = new SparseBitSet();
        BitSet model = new BitSet();
        for (int w2 = 0; w2 < SparseBitSet.BLOCKS_PER_AREA; w2 += 3) {
            int bit = w2 * BLOCK_BITS + w2;
            set.set(bit);
            model.set(bit);
            assertEquals(tightLength(w2), table(set)[0].length, "block " + w2);
            assertSameSet(model, set, "block " + w2);
        }
    }

    /**
     * Every writer that creates or grows an area sizes it to the highest
     * block it holds: single bits, union into an empty and into a smaller
     * set, the difference of a union, a packed operand, the copy of a packed
     * set, unpacking, the packed form, flip, symmetric difference and
     * serialization.
     */
    @Test
    void everyWriterSizesAreasToTheirHighestBlock() {
        Random random = new Random(0xa4eaL);
        for (int trial = 0; trial < 200; ++trial) {
            BitSet low = randomBits(random, 3);
            BitSet high = randomBits(random, SparseBitSet.BLOCKS_PER_AREA);
            BitSet union = (BitSet) low.clone();
            union.or(high);
            BitSet added = (BitSet) high.clone();
            added.andNot(low);
            String at = "trial " + trial;

            assertTight(model(high), high, at + " set");

            SparseBitSet target = model(low);
            target.or(model(high));
            assertTight(target, union, at + " or");

            SparseBitSet diffTarget = model(low);
            IBitSet diff = diffTarget.orDiff(model(high));
            assertTight(diffTarget, union, at + " orDiff target");
            assertTight((SparseBitSet) diff, added, at + " orDiff diff");

            SparseBitSet packed = model(high);
            packed.pack();
            SparseBitSet packedTarget = model(low);
            IBitSet packedDiff = packedTarget.orDiff(packed);
            assertTight(packedTarget, union, at + " orDiff packed");
            assertTight((SparseBitSet) packedDiff, added, at + " orDiff packed diff");
            assertTight(packed.copy(), high, at + " copy of packed");

            SparseBitSet unpacked = model(high);
            unpacked.pack();
            // clearing a clear bit inside the table restores the blocks
            unpacked.clear(high.nextClearBit(0));
            assertFalse(unpacked.isPacked(), at + " unpacked");
            assertTight(unpacked, high, at + " unpack");

            assertTight(SparseBitSet.ofPacked(model(high).toPacked()), high, at + " ofPacked");

            SparseBitSet flipped = new SparseBitSet();
            high.stream().forEach(flipped::flip);
            assertTight(flipped, high, at + " flip");

            SparseBitSet xored = new SparseBitSet();
            xored.xor(model(high));
            assertTight(xored, high, at + " xor");

            assertTight(SerializationUtils.serializedCopy(model(high)), high, at + " serialized");
        }
    }

    /**
     * Random operation sequences over ranges that put blocks at the low and
     * the high end of areas: after every step the set holds the bits of the
     * model, in its order, answers single-bit and neighbour queries as the
     * model does, and has the packed form computed from the model's words.
     */
    @Test
    void randomSequencesKeepTheBitsOrderAndPackedFormOfJavaBitSet() {
        Random random = new Random(0x5a7eL);
        int[] ranges = {BLOCK_BITS * 4, AREA_BITS, AREA_BITS * 3, 1 << 22};
        for (int sequence = 0; sequence < 300; ++sequence) {
            int range = ranges[sequence % ranges.length];
            SparseBitSet[] sets = {new SparseBitSet(), new SparseBitSet()};
            BitSet[] models = {new BitSet(), new BitSet()};
            for (int step = 0; step < 40; ++step) {
                int t = random.nextInt(2);
                SparseBitSet s = sets[t];
                BitSet m = models[t];
                SparseBitSet so = sets[1 - t];
                BitSet mo = models[1 - t];
                String at = "sequence " + sequence + " step " + step;
                switch (random.nextInt(10)) {
                    case 0, 1, 2 -> {
                        for (int i = random.nextInt(30); i >= 0; --i) {
                            int index = random.nextInt(range);
                            s.set(index);
                            m.set(index);
                        }
                    }
                    case 3 -> {
                        for (int i = random.nextInt(10); i >= 0; --i) {
                            int index = m.isEmpty() ? random.nextInt(range)
                                    : m.nextSetBit(random.nextInt(m.length()));
                            if (index >= 0) {
                                s.clear(index);
                                m.clear(index);
                            }
                        }
                    }
                    case 4 -> {
                        s.or(so);
                        m.or(mo);
                    }
                    case 5 -> {
                        BitSet expected = (BitSet) mo.clone();
                        expected.andNot(m);
                        assertSameSet(expected, s.orDiff(so), at + " orDiff diff");
                        m.or(mo);
                    }
                    case 6 -> {
                        s.and(so);
                        m.and(mo);
                    }
                    case 7 -> {
                        s.andNot(so);
                        m.andNot(mo);
                    }
                    case 8 -> {
                        s.xor(so);
                        m.xor(mo);
                    }
                    default -> {
                        s.pack();
                        if (random.nextBoolean()) {
                            sets[t] = s.copy();
                        }
                    }
                }
                assertSameSet(models[t], sets[t], at);
                assertArrayEquals(packedForm(models[t]), sets[t].toPacked(), at + " packed form");
                for (int i = 0; i < 6; ++i) {
                    int index = random.nextInt(range + BLOCK_BITS);
                    BitSet mt = models[t];
                    SparseBitSet st = sets[t];
                    assertEquals(mt.get(index), st.get(index), at + " get " + index);
                    assertEquals(mt.nextSetBit(index), st.nextSetBit(index), at + " next " + index);
                    assertEquals(mt.nextClearBit(index), st.nextClearBit(index),
                            at + " nextClear " + index);
                    assertEquals(mt.previousSetBit(index), st.previousSetBit(index),
                            at + " previous " + index);
                    assertEquals(mt.previousClearBit(index), st.previousClearBit(index),
                            at + " previousClear " + index);
                }
            }
        }
    }

    /**
     * The bytes of the area arrays of random sets, at the full length of
     * {@link SparseBitSet#BLOCKS_PER_AREA} and at the length they have now,
     * with compressed references (16-byte array header, 4-byte slot, 8-byte
     * alignment). Shapes: few blocks low in an area, blocks spread over
     * whole areas, and a dense run. Printed as the measured effect; the
     * tight areas are never larger.
     */
    @Test
    void areaBytesPerSetBeforeAndAfter() {
        Random random = new Random(0xb17eL);
        String[] shapes = {"sparse 40 bits over 2^20", "sparse 400 bits over 2^24",
                "low 3 blocks per area", "dense run 2^16"};
        for (int shape = 0; shape < shapes.length; ++shape) {
            long full = 0;
            long tight = 0;
            int sets = 200;
            for (int n = 0; n < sets; ++n) {
                SparseBitSet set = new SparseBitSet();
                switch (shape) {
                    case 0 -> random.ints(40, 0, 1 << 20).forEach(set::set);
                    case 1 -> random.ints(400, 0, 1 << 24).forEach(set::set);
                    case 2 -> {
                        for (int area = 0; area < 16; ++area) {
                            for (int b = 0; b < 3; ++b) {
                                set.set(area * AREA_BITS + b * BLOCK_BITS + random.nextInt(BLOCK_BITS));
                            }
                        }
                    }
                    default -> {
                        int from = random.nextInt(1 << 20);
                        for (int i = from; i < from + (1 << 16); ++i) {
                            set.set(i);
                        }
                    }
                }
                for (long[][] area : table(set)) {
                    if (area != null) {
                        full += arrayBytes(SparseBitSet.BLOCKS_PER_AREA);
                        tight += arrayBytes(area.length);
                    }
                }
            }
            System.out.println("area bytes per set, " + shapes[shape] + ": before "
                    + full / sets + ", after " + tight / sets);
            assertTrue(tight <= full, shapes[shape]);
        }
    }

    private static long arrayBytes(int slots) {
        return (16L + 4L * slots + 7) & ~7L;
    }

    /** The smallest power of two above {@code w2}: the length of an area whose highest block is w2. */
    private static int tightLength(int w2) {
        int length = 1;
        while (length <= w2) {
            length <<= 1;
        }
        return length;
    }

    /**
     * Checks that {@code set} holds {@code expected} and that each of its
     * areas is as long as its highest present block needs.
     */
    private static void assertTight(SparseBitSet set, BitSet expected, String at) {
        assertSameSet(expected, set, at);
        long[][][] table = table(set);
        for (int w1 = 0; w1 < table.length; ++w1) {
            long[][] area = table[w1];
            if (area == null) {
                continue;
            }
            int highest = -1;
            for (int w2 = 0; w2 < area.length; ++w2) {
                if (area[w2] != null) {
                    highest = w2;
                }
            }
            assertTrue(highest >= 0, at + " area " + w1 + " holds a block");
            assertEquals(tightLength(highest), area.length, at + " area " + w1);
        }
    }

    /** Bits in blocks 0 .. blocks-1 of the first three areas. */
    private static BitSet randomBits(Random random, int blocks) {
        BitSet bits = new BitSet();
        for (int i = random.nextInt(12); i >= 0; --i) {
            int area = random.nextInt(3);
            int block = random.nextInt(blocks);
            bits.set(area * AREA_BITS + block * BLOCK_BITS + random.nextInt(BLOCK_BITS));
        }
        return bits;
    }

    private static SparseBitSet model(BitSet bits) {
        SparseBitSet set = new SparseBitSet();
        bits.stream().forEach(set::set);
        return set;
    }

    /** The packed form of {@link SparseBitSet#toPacked()}, computed from the words of a model. */
    private static long[] packedForm(BitSet bits) {
        long[] words = bits.toLongArray();
        List<Long> packed = new ArrayList<>();
        for (int first = 0; first < words.length; first += WORDS_PER_BLOCK) {
            long mask = 0;
            List<Long> nonZero = new ArrayList<>();
            for (int w3 = 0; w3 < WORDS_PER_BLOCK && first + w3 < words.length; ++w3) {
                if (words[first + w3] != 0) {
                    mask |= 1L << w3;
                    nonZero.add(words[first + w3]);
                }
            }
            if (mask != 0) {
                packed.add(((long) (first / WORDS_PER_BLOCK) << Integer.SIZE) | mask);
                packed.addAll(nonZero);
            }
        }
        return packed.stream().mapToLong(Long::longValue).toArray();
    }

    private static void assertSameSet(BitSet expected, IBitSet actual, String at) {
        assertEquals(expected.cardinality(), actual.cardinality(), at + " cardinality");
        assertEquals(expected.length(), actual.length(), at + " length");
        assertEquals(expected.isEmpty(), actual.isEmpty(), at + " isEmpty");
        int e = expected.nextSetBit(0);
        int a = actual.nextSetBit(0);
        while (e >= 0 || a >= 0) {
            assertEquals(e, a, at + " iteration");
            e = expected.nextSetBit(e + 1);
            a = actual.nextSetBit(a + 1);
        }
    }

    private static long[][][] table(SparseBitSet set) {
        try {
            return (long[][][]) TABLE.get(set);
        } catch (IllegalAccessException e) {
            throw new AssertionError(e);
        }
    }

    private static Field tableField() {
        try {
            Field field = SparseBitSet.class.getDeclaredField("table");
            field.setAccessible(true);
            return field;
        } catch (NoSuchFieldException e) {
            throw new AssertionError(e);
        }
    }
}
