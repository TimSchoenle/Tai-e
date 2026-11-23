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
import java.util.BitSet;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link IBitSet#updateMemoAndCount} and {@link IBitSet#forEachAnd} against
 * {@link BitSet} models, for sparse and regular sets in every combination,
 * with bits in several words, blocks and areas and near the top of the
 * index range.
 */
class BitSetMemoTest {

    private static final int TRIALS = 600;

    /**
     * Bit ranges of the random bits: one word, a few blocks, several areas,
     * and a band that starts far from bit 0.
     */
    private static final int[][] RANGES = {
            {0, 64}, {0, 2000}, {0, 300_000}, {1_000_000, 1_005_000},
    };

    @Test
    void sparseWithSparseMemo() {
        run(SparseBitSet::new, SparseBitSet::new, 1);
    }

    @Test
    void sparseWithRegularMemo() {
        run(SparseBitSet::new, RegularBitSet::new, 2);
    }

    @Test
    void regularWithSparseMemo() {
        run(RegularBitSet::new, SparseBitSet::new, 3);
    }

    private static void run(Supplier<IBitSet> input, Supplier<IBitSet> memo, long seed) {
        Random random = new Random(seed);
        for (int trial = 0; trial < TRIALS; ++trial) {
            int[] range = RANGES[random.nextInt(RANGES.length)];
            BitSet inModel = randomBits(random, range);
            BitSet knownModel = randomBits(random, range);
            BitSet passModel = randomBits(random, range);
            passModel.and(knownModel);
            BitSet accept = randomBits(random, range);
            IBitSet in = of(input, inModel);
            IBitSet known = of(memo, knownModel);
            IBitSet pass = of(memo, passModel);
            // computes and caches the sizes, which the update must invalidate
            assertEquals(knownModel.cardinality(), known.cardinality(), "known size before, trial " + trial);
            assertEquals(passModel.cardinality(), pass.cardinality(), "pass size before, trial " + trial);

            List<Integer> tested = new ArrayList<>();
            int count = in.updateMemoAndCount(known, pass, i -> {
                tested.add(i);
                return accept.get(i);
            });

            List<Integer> wantTested = new ArrayList<>();
            BitSet unknown = (BitSet) inModel.clone();
            unknown.andNot(knownModel);
            unknown.stream().forEach(wantTested::add);
            for (int i : wantTested) {
                knownModel.set(i);
                if (accept.get(i)) {
                    passModel.set(i);
                }
            }
            BitSet passing = (BitSet) inModel.clone();
            passing.and(passModel);
            assertEquals(wantTested, tested, "tested bits, trial " + trial);
            assertEquals(passing.cardinality(), count, "count, trial " + trial);
            assertEquals(knownModel, toModel(known), "known, trial " + trial);
            assertEquals(passModel, toModel(pass), "pass, trial " + trial);
            assertEquals(inModel, toModel(in), "input unchanged, trial " + trial);
            assertEquals(knownModel.cardinality(), known.cardinality(), "known size, trial " + trial);
            assertEquals(passModel.cardinality(), pass.cardinality(), "pass size, trial " + trial);

            List<Integer> visited = new ArrayList<>();
            in.forEachAnd(pass, visited::add);
            List<Integer> wantVisited = new ArrayList<>();
            passing.stream().forEach(wantVisited::add);
            assertEquals(wantVisited, visited, "intersection, trial " + trial);
        }
    }

    /**
     * A bit becomes known only once its test has returned: if the test
     * throws, that bit (and every later one) stays unknown, so a later
     * update tests it again instead of reading it as failed.
     */
    @Test
    void aThrowingTestLeavesItsBitUnknown() {
        List<List<Supplier<IBitSet>>> kinds = List.of(
                List.of(SparseBitSet::new, SparseBitSet::new),
                List.of(SparseBitSet::new, RegularBitSet::new),
                List.of(RegularBitSet::new, SparseBitSet::new));
        int failing = 70;
        BitSet inModel = new BitSet();
        for (int i : new int[]{3, 5, 69, failing, 71, 200_000}) {
            inModel.set(i);
        }
        for (List<Supplier<IBitSet>> kind : kinds) {
            IBitSet in = of(kind.get(0), inModel);
            IBitSet known = kind.get(1).get();
            IBitSet pass = kind.get(1).get();
            RuntimeException thrown = new IllegalStateException("test failed");
            RuntimeException caught = assertThrows(RuntimeException.class,
                    () -> in.updateMemoAndCount(known, pass, i -> {
                        if (i == failing) {
                            throw thrown;
                        }
                        return true;
                    }));
            assertSame(thrown, caught);
            BitSet knownAfter = toModel(known);
            assertTrue(knownAfter.nextSetBit(failing) == -1,
                    "bits known from the failing one on: " + knownAfter);
            assertEquals(knownAfter, toModel(pass), "every known bit passed");

            int count = in.updateMemoAndCount(known, pass, i -> i != failing);
            assertEquals(inModel.cardinality() - 1, count);
            assertEquals(inModel, toModel(known));
            assertFalse(pass.get(failing));
        }
    }

    @Test
    void memoSetsMustBeDifferentSets() {
        for (Supplier<IBitSet> kind : List.<Supplier<IBitSet>>of(SparseBitSet::new, RegularBitSet::new)) {
            IBitSet a = kind.get();
            IBitSet b = kind.get();
            assertThrows(IllegalArgumentException.class,
                    () -> a.updateMemoAndCount(a, b, i -> true));
            assertThrows(IllegalArgumentException.class,
                    () -> a.updateMemoAndCount(b, a, i -> true));
            assertThrows(IllegalArgumentException.class,
                    () -> a.updateMemoAndCount(b, b, i -> true));
        }
    }

    private static BitSet randomBits(Random random, int[] range) {
        BitSet bits = new BitSet();
        int width = range[1] - range[0];
        int n = random.nextInt(4) == 0 ? 0 : random.nextInt(Math.min(width, 400));
        boolean clustered = random.nextBoolean();
        int start = random.nextInt(width);
        for (int i = 0; i < n; ++i) {
            int offset = clustered
                    ? (start + random.nextInt(Math.min(width, 700))) % width
                    : random.nextInt(width);
            bits.set(range[0] + offset);
        }
        return bits;
    }

    private static IBitSet of(Supplier<IBitSet> kind, BitSet model) {
        IBitSet set = kind.get();
        model.stream().forEach(set::set);
        return set;
    }

    private static BitSet toModel(IBitSet set) {
        BitSet model = new BitSet();
        for (int i = set.nextSetBit(0); i != -1; i = set.nextSetBit(i + 1)) {
            model.set(i);
        }
        return model;
    }
}
