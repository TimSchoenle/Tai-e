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
import pascal.taie.util.Indexer;

import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link IBitSet#orDiff(IBitSet, IBitSet)} and
 * {@link SetEx#addAllDiff(java.util.Collection, SetEx)} give the same bits, in the
 * same order, as the allocating forms, and write a reusable diff set in
 * place instead of allocating one.
 */
public class OrDiffReuseTest {

    private static final int ROUNDS = 2000;

    private static final int ALLOCATION_REPS = 1000;

    private static Object sink;

    @Test
    void reusedDiffMatchesFreshDiff() {
        Random random = new Random(115);
        RegularBitSet scratch = new RegularBitSet();
        for (int round = 0; round < ROUNDS; ++round) {
            IBitSet base = randomSet(random);
            IBitSet added = randomSet(random);
            if (random.nextInt(4) == 0) {
                // a scratch set wider than any diff of this round
                scratch.set(10_000 + random.nextInt(5_000));
            }
            IBitSet expectedBase = base.copy();
            IBitSet expected = expectedBase.orDiff(added);
            IBitSet actual = base.orDiff(added, scratch);
            assertSame(scratch, actual);
            assertEquals(bits(expected), bits(actual));
            assertEquals(expected, actual);
            assertEquals(expected.hashCode(), actual.hashCode());
            assertEquals(expected.cardinality(), actual.cardinality());
            assertEquals(expected.length(), actual.length());
            assertEquals(expectedBase, base);
            // the reused set keeps the invariants of a bit set: it grows
            // and compares like a fresh one
            int extra = random.nextInt(12_000);
            assertEquals(expected.set(extra), actual.set(extra));
            assertEquals(expected, actual);
        }
    }

    @Test
    void orDiffWithItselfClearsTheReusedDiff() {
        IBitSet set = IBitSet.of(1, 333, 66666);
        RegularBitSet scratch = (RegularBitSet) IBitSet.of(5, 70000);
        IBitSet diff = set.orDiff(set, scratch);
        assertSame(scratch, diff);
        assertTrue(diff.isEmpty());
        assertEquals(IBitSet.of(1, 333, 66666), set);
    }

    @Test
    void diffIsNotReusedWhenItIsAnOperandOrNotRegular() {
        IBitSet set = IBitSet.of(1, 333);
        IBitSet added = IBitSet.of(333, 777);
        IBitSet asThis = set.orDiff(added, set);
        assertNotSame(set, asThis);
        assertEquals(IBitSet.of(777), asThis);
        IBitSet asSet = IBitSet.of(1).orDiff(added, added);
        assertNotSame(added, asSet);
        assertEquals(IBitSet.of(333, 777), asSet);
        assertEquals(IBitSet.of(333, 777), added);
        SparseBitSet sparse = new SparseBitSet();
        sparse.set(9);
        IBitSet intoSparse = IBitSet.of(1).orDiff(IBitSet.of(1, 2), sparse);
        assertNotSame(sparse, intoSparse);
        assertEquals(IBitSet.of(2), intoSparse);
        assertTrue(sparse.get(9));
    }

    @Test
    void reusedDiffAllocatesNothing() {
        com.sun.management.ThreadMXBean bean =
                (com.sun.management.ThreadMXBean) ManagementFactory.getThreadMXBean();
        IBitSet base = new RegularBitSet();
        // one new bit far from bit 0: a fresh diff holds all words below it
        IBitSet added = IBitSet.of(64 * 1000);
        RegularBitSet scratch = new RegularBitSet();
        long fresh = 0;
        long reused = 0;
        for (int warm = 0; warm < 3; ++warm) {
            fresh = bytesPerCall(bean, base, added, null);
            reused = bytesPerCall(bean, base, added, scratch);
        }
        assertTrue(fresh >= 8 * 1000, "a fresh diff allocated " + fresh + " bytes");
        assertEquals(0, reused, "a reused diff allocated " + reused + " bytes per call");
    }

    @Test
    void addAllDiffReusesADiffOfTheSameContext() {
        Indexer<Integer> indexer = new IntIndexer();
        Random random = new Random(1150);
        IndexerBitSet<Integer> scratch = new IndexerBitSet<>(indexer, false);
        for (int round = 0; round < ROUNDS; ++round) {
            SetEx<Integer> base = randomSet(indexer, random);
            SetEx<Integer> added = randomSet(indexer, random);
            SetEx<Integer> expectedBase = base.copy();
            SetEx<Integer> expected = expectedBase.addAllDiff(added);
            SetEx<Integer> actual = base.addAllDiff(added, scratch);
            assertSame(scratch, actual);
            assertEquals(new ArrayList<>(expected), new ArrayList<>(actual));
            assertEquals(new ArrayList<>(expectedBase), new ArrayList<>(base));
        }
    }

    @Test
    void addAllDiffLeavesADiffOfAnotherContextUnchanged() {
        Indexer<Integer> indexer = new IntIndexer();
        IndexerBitSet<Integer> base = new IndexerBitSet<>(indexer, false);
        base.add(1);
        IndexerBitSet<Integer> added = new IndexerBitSet<>(indexer, false);
        added.add(1);
        added.add(70);
        IndexerBitSet<Integer> otherContext = new IndexerBitSet<>(new IntIndexer(), false);
        otherContext.add(5);
        SetEx<Integer> diff = base.addAllDiff(added, otherContext);
        assertNotSame(otherContext, diff);
        assertEquals(List.of(70), new ArrayList<>(diff));
        assertEquals(List.of(5), new ArrayList<>(otherContext));
        assertEquals(List.of(1, 70), new ArrayList<>(base));
    }

    /**
     * @return the bytes this thread allocated per call of the diff of
     * {@code added} into a cleared {@code base}: the allocating form when
     * {@code scratch} is null
     */
    private static long bytesPerCall(com.sun.management.ThreadMXBean bean,
                                     IBitSet base, IBitSet added, RegularBitSet scratch) {
        long before = bean.getCurrentThreadAllocatedBytes();
        for (int i = 0; i < ALLOCATION_REPS; ++i) {
            base.clear();
            sink = scratch == null ? base.orDiff(added) : base.orDiff(added, scratch);
        }
        return (bean.getCurrentThreadAllocatedBytes() - before) / ALLOCATION_REPS;
    }

    private static IBitSet randomSet(Random random) {
        RegularBitSet set = new RegularBitSet();
        int bound = 1 + random.nextInt(4) * 3000;
        int n = random.nextInt(8);
        for (int i = 0; i < n; ++i) {
            set.set(random.nextInt(bound));
        }
        return set;
    }

    private static SetEx<Integer> randomSet(Indexer<Integer> indexer, Random random) {
        IndexerBitSet<Integer> set = new IndexerBitSet<>(indexer, false);
        int bound = 1 + random.nextInt(4) * 3000;
        int n = random.nextInt(8);
        for (int i = 0; i < n; ++i) {
            set.add(random.nextInt(bound));
        }
        return set;
    }

    private static List<Integer> bits(IBitSet set) {
        List<Integer> bits = new ArrayList<>();
        for (int i = set.nextSetBit(0); i >= 0; i = set.nextSetBit(i + 1)) {
            bits.add(i);
        }
        return bits;
    }

    /**
     * Numbers each integer by itself.
     */
    private static final class IntIndexer implements Indexer<Integer> {

        @Override
        public int getIndex(Integer o) {
            return o;
        }

        @Override
        public Integer getObject(int index) {
            return index;
        }
    }
}
