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

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The reads that pair the words of two sets ({@link SparseBitSet#contains},
 * {@link SparseBitSet#orSummary}, {@link SparseBitSet#minus} and
 * {@link SparseBitSet#nextSetBit}) give the same answers for every form of
 * the two sets (packed or with blocks) as a {@link BitSet} model, on pairs
 * that are sparse, dense, disjoint, equal, nested and hub-sized, and leave
 * the forms as they were.
 */
class SparseBitSetMergeWalkTest {

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** The objects of a hub-sized points-to set. */
    private static final int HUB_BITS = 1 << 18;

    private static final int PAIRS = 240;

    private enum Shape {
        SPARSE, DENSE, DISJOINT, EQUAL, SUBSET, SUPERSET, HUB_SUBSET, HUB_EQUAL, HUB_PLUS_ONE
    }

    private record Pair(BitSet a, BitSet b) {
    }

    private static BitSet randomBits(Random random, int range, int n, boolean clustered) {
        BitSet bits = new BitSet();
        int base = random.nextInt(range);
        for (int i = 0; i < n; i++) {
            bits.set(clustered
                    ? Math.min(range - 1, base + random.nextInt(4 * BLOCK_BITS))
                    : random.nextInt(range));
        }
        return bits;
    }

    /** A random subset of {@code bits}: each bit kept with a chance of 7/8. */
    private static BitSet subsetOf(Random random, BitSet bits) {
        BitSet subset = new BitSet();
        for (int i = bits.nextSetBit(0); i >= 0; i = bits.nextSetBit(i + 1)) {
            if (random.nextInt(8) != 0) {
                subset.set(i);
            }
        }
        return subset;
    }

    private static Pair pair(Random random, Shape shape) {
        int range = 1 << (8 + random.nextInt(14));
        switch (shape) {
            case SPARSE:
                return new Pair(randomBits(random, range, random.nextInt(60), false),
                        randomBits(random, range, random.nextInt(60), false));
            case DENSE:
                return new Pair(randomBits(random, range, range / 2, false),
                        randomBits(random, range, range / 2, random.nextBoolean()));
            case DISJOINT: {
                BitSet a = randomBits(random, range, random.nextInt(400), random.nextBoolean());
                BitSet b = randomBits(random, range, random.nextInt(400), random.nextBoolean());
                b.andNot(a);
                return new Pair(a, b);
            }
            case EQUAL: {
                BitSet a = randomBits(random, range, random.nextInt(2000), random.nextBoolean());
                return new Pair(a, (BitSet) a.clone());
            }
            case SUBSET: {
                BitSet a = randomBits(random, range, random.nextInt(2000), random.nextBoolean());
                return new Pair(a, subsetOf(random, a));
            }
            case SUPERSET: {
                BitSet b = randomBits(random, range, random.nextInt(2000), random.nextBoolean());
                return new Pair(subsetOf(random, b), b);
            }
            case HUB_SUBSET: {
                BitSet a = randomBits(random, HUB_BITS, HUB_BITS / 2 + random.nextInt(HUB_BITS / 2), false);
                return new Pair(a, subsetOf(random, a));
            }
            case HUB_EQUAL: {
                BitSet a = randomBits(random, HUB_BITS, HUB_BITS / 2 + random.nextInt(HUB_BITS / 2), false);
                return new Pair(a, (BitSet) a.clone());
            }
            case HUB_PLUS_ONE: {
                BitSet a = randomBits(random, HUB_BITS, HUB_BITS / 2 + random.nextInt(HUB_BITS / 2), false);
                BitSet b = subsetOf(random, a);
                b.set(HUB_BITS + random.nextInt(HUB_BITS));
                return new Pair(a, b);
            }
            default:
                throw new AssertionError(shape);
        }
    }

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

    private static long summary(BitSet union) {
        SparseBitSet set = sparse(union, false);
        return ((long) set.cardinality() << Integer.SIZE) | (set.hashCode() & 0xFFFFFFFFL);
    }

    @Test
    void pairedReadsMatchTheModelInEveryForm() {
        Random random = new Random(0x3e7aL);
        Shape[] shapes = Shape.values();
        for (int p = 0; p < PAIRS; p++) {
            Shape shape = shapes[p % shapes.length];
            Pair pair = pair(random, shape);
            BitSet aContainsB = (BitSet) pair.b().clone();
            aContainsB.andNot(pair.a());
            boolean expectedContains = aContainsB.isEmpty();
            BitSet union = (BitSet) pair.a().clone();
            union.or(pair.b());
            long expectedSummary = summary(union);
            BitSet aMinusB = (BitSet) pair.a().clone();
            aMinusB.andNot(pair.b());
            long[] expectedMinus = sparse(aMinusB, false).toPacked();
            int range = Math.max(pair.a().length(), 1) + 2 * BLOCK_BITS;
            for (int forms = 0; forms < 4; forms++) {
                boolean aPacked = (forms & 1) != 0;
                boolean bPacked = (forms & 2) != 0;
                String at = "pair " + p + " " + shape + " a packed " + aPacked
                        + " b packed " + bPacked;
                SparseBitSet a = sparse(pair.a(), aPacked);
                SparseBitSet b = sparse(pair.b(), bPacked);
                assertEquals(expectedContains, a.contains(b), at + ": contains");
                assertEquals(expectedSummary, a.orSummary(b), at + ": orSummary");
                SparseBitSet minus = a.minus(b);
                assertFalse(minus.isPacked(), at + ": minus form");
                assertArrayEquals(expectedMinus, minus.toPacked(), at + ": minus");
                for (int k = 0; k < 32; k++) {
                    int from = random.nextInt(range);
                    assertEquals(pair.a().nextSetBit(from), a.nextSetBit(from),
                            at + ": nextSetBit " + from);
                }
                assertEquals(aPacked, a.isPacked(), at + ": a form");
                assertEquals(bPacked, b.isPacked(), at + ": b form");
            }
        }
    }

    /**
     * Times {@link SparseBitSet#contains} of a packed held set drawn from 131k
     * to 262k objects over an equal set, packed or with blocks (the exact check of a
     * hit of the points-to set interner), and prints the time per call.
     */
    @Test
    void measuresContainsOfAHubSizedHeldSet() {
        Random random = new Random(0x51deL);
        BitSet bits = randomBits(random, 1 << 20, (1 << 17) + random.nextInt(1 << 17), false);
        SparseBitSet held = sparse(bits, true);
        SparseBitSet tableQuery = sparse(bits, false);
        SparseBitSet packedQuery = sparse(bits, true);
        assertTrue(held.isPacked());
        int rounds = 400;
        for (SparseBitSet query : new SparseBitSet[] {tableQuery, packedQuery}) {
            for (int warm = 0; warm < rounds; warm++) {
                assertTrue(held.contains(query));
            }
            long start = System.nanoTime();
            for (int round = 0; round < rounds; round++) {
                assertTrue(held.contains(query));
            }
            long perCall = (System.nanoTime() - start) / rounds;
            System.out.println("mergewalk contains held=" + held.cardinality()
                    + " query packed=" + query.isPacked() + " ns/call=" + perCall);
        }
    }
}
