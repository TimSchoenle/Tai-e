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

package pascal.taie.analysis.pta.pts;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.TestElements;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The interner's copies counted by the forms of the held set and of the
 * delta.
 */
class PointsToSetInternerFormCountersTest {

    private static final int OBJECTS = 64;

    private final CSObj[] objs = TestElements.objects(OBJECTS);

    private final PointsToSetFactory factory =
            new PointsToSetFactory(TestElements.indexer(objs));

    private PointsToSet set(int from, int to) {
        PointsToSet set = factory.make();
        for (int i = from; i < to; ++i) {
            set.addObject(objs[i]);
        }
        return set;
    }

    /**
     * Lets two pointers hold the same shared set, then changes the first
     * by {@code delta}, which copies the held set.
     */
    private static void copyShared(PointsToSetInterner interner, int first,
                                   PointsToSet held, PointsToSet delta) {
        Pointer p = TestElements.pointer(first);
        Pointer q = TestElements.pointer(first + 1);
        interner.addAllDiff(p, held);
        interner.addAllDiff(q, held);
        interner.addAllDiff(p, delta);
    }

    @Test
    void countsCopiesByHeldAndDeltaForm() {
        PointsToSetInterner interner = new PointsToSetInterner(factory);
        interner.enableFormCounters();
        copyShared(interner, 0, set(0, 1), set(1, 2));
        copyShared(interner, 2, set(0, OBJECTS - 1), set(OBJECTS - 1, OBJECTS));
        // the first change of each pointer copies the shared empty set,
        // except the second taking the large set: it adopts the shared
        // set equal to it, which is no copy
        String line = interner.formCopiesLine();
        assertTrue(line.startsWith("copies_small_small=3/1 copies_small_large=1/0"
                + " copies_large_small=1/" + (OBJECTS - 1) + " copies_large_large=0/0 "), line);
        assertEquals(5, interner.counters().copies());
        assertEquals(1, interner.counters().adoptions());
        long largeHeld = PointsToSetInterner.copiedBytes(set(0, OBJECTS - 1));
        assertEquals(largeHeld, copiedBytes(line, "large_small"));
        assertEquals(0, copiedBytes(line, "large_large"));
        assertTrue(copiedBytes(line, "small_small") > 0, line);
        assertTrue(copiedBytes(line, "small_large") > 0, line);
    }

    @Test
    void estimatesALargeHeldSetByItsPackedWords() {
        long large = PointsToSetInterner.copiedBytes(set(0, OBJECTS - 1));
        long small = PointsToSetInterner.copiedBytes(set(0, 2));
        // the 63 dense objects fit in one packed block: fewer bytes than
        // one reference per object, more than an empty array
        assertTrue(large > 16 && large < 4L * (OBJECTS - 1), "large " + large);
        assertTrue(small > 16 && small < large, "small " + small);
    }

    private static long copiedBytes(String line, String form) {
        String key = "copied_bytes_" + form + "=";
        int at = line.indexOf(key);
        assertTrue(at >= 0, line);
        int end = line.indexOf(' ', at);
        return Long.parseLong(line.substring(at + key.length(), end < 0 ? line.length() : end));
    }

    @Test
    void countsNothingWhenOff() {
        PointsToSetInterner interner = new PointsToSetInterner(factory);
        copyShared(interner, 0, set(0, 1), set(1, 2));
        assertEquals("", interner.formCopiesLine());
    }
}
