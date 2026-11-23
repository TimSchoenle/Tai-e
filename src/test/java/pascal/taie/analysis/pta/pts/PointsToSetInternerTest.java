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

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PointsToSetInternerTest {

    private static final int OBJECTS = 64;

    private final CSObj[] objs = TestElements.objects(OBJECTS);

    private final PointsToSetFactory factory =
            new PointsToSetFactory(TestElements.indexer(objs));

    private final PointsToSetInterner interner = new PointsToSetInterner(factory);

    /**
     * A set built by adding the objects in the given order.
     */
    private PointsToSet small(int... indexes) {
        PointsToSet set = factory.make();
        for (int i : indexes) {
            set.addObject(objs[i]);
        }
        return set;
    }

    /**
     * A set in the large (bit set) form holding exactly the given objects.
     */
    private PointsToSet large(int... indexes) {
        PointsToSet set = factory.make();
        for (CSObj o : objs) {
            set.addObject(o);
        }
        Set<CSObj> keep = Collections.newSetFromMap(new IdentityHashMap<>());
        for (int i : indexes) {
            keep.add(objs[i]);
        }
        set.removeIf(o -> !keep.contains(o));
        assertTrue(((DelegatePointsToSet) set).isLarge());
        return set;
    }

    private static List<Integer> sequence(PointsToSet set) {
        List<Integer> indexes = new ArrayList<>();
        for (CSObj o : set) {
            indexes.add(o.getIndex());
        }
        return indexes;
    }

    private static boolean isLarge(PointsToSet set) {
        return ((DelegatePointsToSet) set).isLarge();
    }

    @Test
    void equalSetsAreShared() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2));
        interner.addAllDiff(p2, small(1, 2));
        assertSame(p1.getPointsToSet(), p2.getPointsToSet());
        assertTrue(p1.getPointsToSet().isShared());
        assertEquals(List.of(1, 2), sequence(p2.getPointsToSet()));
    }

    @Test
    void sharedSetRefusesEveryMutation() {
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, small(1, 2));
        PointsToSet shared = p.getPointsToSet();
        assertThrows(IllegalStateException.class, () -> shared.addObject(objs[3]));
        assertThrows(IllegalStateException.class, () -> shared.addAll(small(3)));
        assertThrows(IllegalStateException.class, () -> shared.addAllDiff(small(3)));
        assertThrows(IllegalStateException.class, () -> shared.removeIf(o -> true));
        assertEquals(List.of(1, 2), sequence(shared));
        PointsToSet copy = shared.copy();
        assertFalse(copy.isShared());
        assertTrue(copy.addObject(objs[3]));
        assertEquals(List.of(1, 2), sequence(shared));
    }

    @Test
    void changeOfOnePointerDoesNotLeakIntoAnother() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2));
        interner.addAllDiff(p2, small(1, 2));
        PointsToSet before = p2.getPointsToSet();
        PointsToSet diff = interner.addAllDiff(p1, small(2, 3));
        assertEquals(List.of(3), sequence(diff));
        assertEquals(List.of(1, 2, 3), sequence(p1.getPointsToSet()));
        assertSame(before, p2.getPointsToSet());
        assertEquals(List.of(1, 2), sequence(p2.getPointsToSet()));
    }

    @Test
    void iterationOrderIsPartOfTheIdentity() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2));
        interner.addAllDiff(p2, small(2, 1));
        assertNotSame(p1.getPointsToSet(), p2.getPointsToSet());
        assertEquals(List.of(1, 2), sequence(p1.getPointsToSet()));
        assertEquals(List.of(2, 1), sequence(p2.getPointsToSet()));
    }

    @Test
    void equalHashesAreComparedExactly() {
        // 31 * (31 * 2 + 0) + 31 == 31 * (31 * 2 + 1) + 0
        PointsToSet a = small(0, 31);
        PointsToSet b = small(1, 0);
        assertEquals(((DelegatePointsToSet) a).sequenceHash(),
                ((DelegatePointsToSet) b).sequenceHash());
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, a);
        interner.addAllDiff(p2, b);
        assertNotSame(p1.getPointsToSet(), p2.getPointsToSet());
        assertEquals(List.of(0, 31), sequence(p1.getPointsToSet()));
        assertEquals(List.of(1, 0), sequence(p2.getPointsToSet()));
    }

    @Test
    void turningLargeWithoutNewObjectsIsKept() {
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, small(3, 2, 1));
        PointsToSet reference = small(3, 2, 1);
        PointsToSet referenceDiff = reference.addAllDiff(large(1, 2, 3));
        PointsToSet diff = interner.addAllDiff(p, large(1, 2, 3));
        assertTrue(referenceDiff.isEmpty());
        assertTrue(diff.isEmpty());
        assertTrue(isLarge(reference));
        assertTrue(isLarge(p.getPointsToSet()));
        assertEquals(sequence(reference), sequence(p.getPointsToSet()));
        assertEquals(List.of(1, 2, 3), sequence(p.getPointsToSet()));
    }

    @Test
    void fullSmallSetTurnsLargeOnAKnownObject() {
        int[] full = {8, 7, 6, 5, 4, 3, 2, 1};
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, small(full));
        assertFalse(isLarge(p.getPointsToSet()));
        PointsToSet reference = small(full);
        PointsToSet referenceDiff = reference.addAllDiff(small(5));
        PointsToSet diff = interner.addAllDiff(p, small(5));
        assertTrue(referenceDiff.isEmpty());
        assertTrue(diff.isEmpty());
        assertEquals(isLarge(reference), isLarge(p.getPointsToSet()));
        assertEquals(sequence(reference), sequence(p.getPointsToSet()));
    }

    @Test
    void releasedSetsLeaveTheTable() {
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, factory.make());
        int base = interner.size();
        for (int i = 0; i < OBJECTS; ++i) {
            interner.addAllDiff(p, small(i));
            assertEquals(base + 1, interner.size(), "after object " + i);
        }
    }

    /**
     * Random sequences of changes on a few pointers: each pointer's set and
     * each difference equal those of an unshared set changed in place, and
     * the table holds exactly the distinct held sets plus the empty set.
     */
    @Test
    void matchesMutableSets() {
        for (long seed = 1; seed <= 40; ++seed) {
            Random random = new Random(seed);
            PointsToSetInterner sharing = new PointsToSetInterner(factory);
            int n = 12;
            Pointer[] pointers = new Pointer[n];
            PointsToSet[] references = new PointsToSet[n];
            for (int i = 0; i < n; ++i) {
                pointers[i] = TestElements.pointer(i);
                references[i] = factory.make();
            }
            PointsToSet empty = sharing.addAllDiff(TestElements.pointer(n), factory.make());
            for (int step = 0; step < 600; ++step) {
                int i = random.nextInt(n);
                int[] picked = pick(random);
                boolean asLarge = random.nextInt(4) == 0;
                PointsToSet referenceDiff = references[i].addAllDiff(
                        asLarge ? large(picked) : small(picked));
                PointsToSet diff = sharing.addAllDiff(pointers[i],
                        asLarge ? large(picked) : small(picked));
                String at = "seed " + seed + " step " + step;
                assertEquals(sequence(referenceDiff), sequence(diff), at);
                for (int j = 0; j < n; ++j) {
                    PointsToSet held = pointers[j].getPointsToSet();
                    if (held == null) {
                        assertTrue(references[j].isEmpty(), at);
                        continue;
                    }
                    assertEquals(sequence(references[j]), sequence(held), at);
                    assertEquals(isLarge(references[j]), isLarge(held), at);
                }
            }
            Set<PointsToSet> held = Collections.newSetFromMap(new IdentityHashMap<>());
            held.add(empty);
            for (Pointer p : pointers) {
                if (p.getPointsToSet() != null) {
                    held.add(p.getPointsToSet());
                }
            }
            assertEquals(held.size(), sharing.size(), "seed " + seed);
            for (PointsToSet a : held) {
                for (PointsToSet b : held) {
                    assertTrue(a == b || !((DelegatePointsToSet) a)
                            .sameSequence((DelegatePointsToSet) b), "seed " + seed);
                }
            }
        }
    }

    /**
     * Many distinct sets in a table that starts at two slots, so it grows
     * several times and deletes across collisions and the wrap-around; after
     * each step every held set is still found, and the table holds exactly
     * the distinct held sets plus the empty set.
     */
    @Test
    void tableGrowsAndDeletesUnderCollisions() {
        for (long seed = 1; seed <= 3; ++seed) {
            Random random = new Random(seed);
            PointsToSetInterner sharing = new PointsToSetInterner(factory, 2);
            int n = 700;
            Pointer[] pointers = new Pointer[n];
            for (int i = 0; i < n; ++i) {
                pointers[i] = TestElements.pointer(i);
                sharing.addAllDiff(pointers[i], small(i % OBJECTS, (i / OBJECTS) % OBJECTS));
            }
            assertTrue(sharing.capacity() >= 2 * sharing.size(), "seed " + seed);
            List<Integer> order = new ArrayList<>();
            for (int i = 0; i < n; ++i) {
                order.add(i);
            }
            Collections.shuffle(order, random);
            for (int i : order) {
                // grows the pointer's set, which frees the old shared one
                sharing.addAllDiff(pointers[i], small(OBJECTS - 1, OBJECTS - 2, OBJECTS - 3));
                String at = "seed " + seed + " pointer " + i;
                Set<PointsToSet> held = Collections.newSetFromMap(new IdentityHashMap<>());
                held.add(sharing.find(factory.make()));
                for (Pointer p : pointers) {
                    PointsToSet set = p.getPointsToSet();
                    held.add(set);
                    // an equal fresh set finds the held one
                    assertSame(set, sharing.find(set.copy()), at);
                }
                assertEquals(held.size(), sharing.size(), at);
            }
        }
    }

    private static int[] pick(Random random) {
        int size = 1 + random.nextInt(random.nextInt(3) == 0 ? 12 : 4);
        int[] picked = new int[size];
        for (int k = 0; k < size; ++k) {
            // few distinct objects, so sets repeat and get shared
            picked[k] = random.nextInt(14);
        }
        return picked;
    }
}
