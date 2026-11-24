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
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks the state of {@link SparseBitSet} (hash code, size, length,
 * cardinality, emptiness) that {@code set(int)}, {@code or} and
 * {@code orDiff} keep up to date word by word.
 * <p>
 * The reference is a twin set that receives the same operations and whose
 * state is marked out of date after every change those writers make, so
 * that it is recomputed on the next read, as it was before they kept the
 * state up to date. The size alone cannot be checked against a recompute
 * at any time: a recompute counts the all-zero blocks it removes, so a
 * second recompute may give a smaller size.
 */
class SparseBitSetStateTest {

    private static final int SEQUENCES = 300;

    private static final int STEPS = 80;

    /** The bits of one block of a sparse bit set, from its geometry. */
    private static final int BLOCK_BITS = 1 << (SparseBitSet.SHIFT2 + SparseBitSet.SHIFT3);

    /** Index ranges: one block, a few blocks, many blocks and areas. */
    private static final int[] RANGES = {BLOCK_BITS, 4 * BLOCK_BITS, 1 << 18, 1 << 22};

    @Test
    void randomSequencesMatchTheRecomputingTwin() {
        Random random = new Random(0x57a7eL);
        int reads = 0;
        int validReads = 0;
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            int range = RANGES[sequence % RANGES.length];
            SparseBitSet[] sets = {new SparseBitSet(), new SparseBitSet()};
            SparseBitSet[] twins = {new SparseBitSet(), new SparseBitSet()};
            for (int step = 0; step < STEPS; step++) {
                int target = random.nextInt(2);
                SparseBitSet s = sets[target];
                SparseBitSet t = twins[target];
                SparseBitSet other = sets[1 - target];
                SparseBitSet otherTwin = twins[1 - target];
                String at = "sequence " + sequence + " step " + step;
                switch (random.nextInt(14)) {
                    case 0, 1, 2, 3 -> {
                        int count = 1 + random.nextInt(12);
                        for (int i = 0; i < count; i++) {
                            int index = random.nextInt(range);
                            boolean changed = t.set(index);
                            invalidateIf(changed, t);
                            assertEquals(changed, s.set(index), at + " set " + index);
                        }
                    }
                    case 4, 5 -> {
                        boolean changed = t.or(otherTwin);
                        invalidateIf(changed, t);
                        assertEquals(changed, s.or(other), at + " or");
                    }
                    case 6 -> {
                        IBitSet twinDiff = t.orDiff(otherTwin);
                        invalidateIf(!twinDiff.isEmpty(), t);
                        assertSameState(twinDiff, s.orDiff(other), at + " orDiff diff");
                    }
                    case 7 -> {
                        // clearing a bit may leave an all-zero block in place
                        int count = 1 + random.nextInt(4);
                        for (int i = 0; i < count; i++) {
                            int index = random.nextInt(range);
                            assertEquals(t.clear(index), s.clear(index), at + " clear " + index);
                        }
                    }
                    case 8 -> {
                        int index = random.nextInt(range);
                        t.flip(index);
                        s.flip(index);
                    }
                    case 9 -> assertEquals(t.and(otherTwin), s.and(other), at + " and");
                    case 10 -> assertEquals(t.andNot(otherTwin), s.andNot(other), at + " andNot");
                    case 11 -> assertEquals(t.xor(otherTwin), s.xor(other), at + " xor");
                    case 12 -> {
                        if (random.nextInt(4) == 0) {
                            t.clear();
                            s.clear();
                        } else {
                            t = t.copy();
                            invalidate(t);
                            s = s.copy();
                        }
                    }
                    default -> {
                        t = new SparseBitSet();
                        t.setTo(otherTwin);
                        invalidate(t);
                        s = new SparseBitSet();
                        s.setTo(other);
                    }
                }
                sets[target] = s;
                twins[target] = t;
                // reading is skipped now and then, so that writers also
                // meet a state that is already out of date
                if (random.nextInt(5) != 0) {
                    ++reads;
                    if (isValid(s)) {
                        ++validReads;
                    }
                    assertSameState(t, s, at);
                }
            }
        }
        // the word-by-word path must actually run, not only invalidate
        assertTrue(validReads * 3 > reads, validReads + " of " + reads + " reads met a valid state");
    }

    /**
     * A recompute that found an all-zero block counts it in the size and
     * removes it from the set: the next word-by-word update must not start
     * from that size.
     */
    @Test
    void setAfterRemovedZeroBlockKeepsTheRecomputedSize() {
        SparseBitSet s = new SparseBitSet();
        s.set(0);
        s.set(BLOCK_BITS);
        s.clear(0);
        assertEquals(2 * BLOCK_BITS, s.size());
        s.set(BLOCK_BITS + 1);
        assertRecomputedState(s, "set after a removed zero block");
        assertEquals(BLOCK_BITS, s.size());
    }

    @Test
    void orIntoAnEmptySetKeepsTheRecomputedState() {
        SparseBitSet source = new SparseBitSet();
        source.set(3);
        source.set(5 * BLOCK_BITS + 70);
        SparseBitSet s = new SparseBitSet();
        assertEquals(0, s.size());
        s.or(source);
        assertTrue(isValid(s), "or keeps the state valid");
        assertRecomputedState(s, "or into an empty set");
        assertEquals(source.hashCode(), s.hashCode());
        assertEquals(2 * BLOCK_BITS, s.size());
    }

    /**
     * Reads the state of {@code s} as its writers left it, then forces a
     * full recompute and asserts that it gives the same state.
     */
    private static void assertRecomputedState(IBitSet set, String at) {
        SparseBitSet s = (SparseBitSet) set;
        int hash = s.hashCode();
        int size = s.size();
        int length = s.length();
        int cardinality = s.cardinality();
        boolean empty = s.isEmpty();
        invalidate(s);
        assertEquals(s.hashCode(), hash, at + " hashCode");
        assertEquals(s.size(), size, at + " size");
        assertEquals(s.length(), length, at + " length");
        assertEquals(s.cardinality(), cardinality, at + " cardinality");
        assertEquals(s.isEmpty(), empty, at + " isEmpty");
    }

    private static void assertSameState(IBitSet expected, IBitSet actual, String at) {
        assertEquals(expected.hashCode(), actual.hashCode(), at + " hashCode");
        assertEquals(expected.size(), actual.size(), at + " size");
        assertEquals(expected.length(), actual.length(), at + " length");
        assertEquals(expected.cardinality(), actual.cardinality(), at + " cardinality");
        assertEquals(expected.isEmpty(), actual.isEmpty(), at + " isEmpty");
    }

    @Test
    void setInANewBlockAndTheLastWordKeepsAValidState() {
        SparseBitSet s = new SparseBitSet(1 << 16);
        s.set(5);
        assertEquals(BLOCK_BITS, s.size());
        s.set(3 * BLOCK_BITS + 9);
        s.set(3 * BLOCK_BITS + 40);
        assertTrue(isValid(s), "set keeps the state valid");
        SparseBitSet expected = new SparseBitSet();
        expected.set(5);
        expected.set(3 * BLOCK_BITS + 9);
        expected.set(3 * BLOCK_BITS + 40);
        assertSameState(expected, s, "set in a new block and the last word");
    }

    private static boolean isValid(SparseBitSet s) {
        try {
            Field stateField = SparseBitSet.class.getDeclaredField("state");
            stateField.setAccessible(true);
            Object state = stateField.get(s);
            Field valid = state.getClass().getDeclaredField("valid");
            valid.setAccessible(true);
            return valid.getBoolean(state);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("cannot reach the state of SparseBitSet", e);
        }
    }

    private static void invalidateIf(boolean changed, SparseBitSet s) {
        if (changed) {
            invalidate(s);
        }
    }

    /** Marks the state of {@code s} out of date, as every other writer does. */
    private static void invalidate(SparseBitSet s) {
        try {
            Field stateField = SparseBitSet.class.getDeclaredField("state");
            stateField.setAccessible(true);
            Object state = stateField.get(s);
            Field valid = state.getClass().getDeclaredField("valid");
            valid.setAccessible(true);
            valid.setBoolean(state, false);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("cannot reach the state of SparseBitSet", e);
        }
    }
}
