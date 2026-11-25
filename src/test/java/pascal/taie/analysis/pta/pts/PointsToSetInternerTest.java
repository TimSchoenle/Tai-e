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
import static org.junit.jupiter.api.Assertions.assertNull;
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
    void unsharingReleasesTheHeldSet() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2));
        interner.addAllDiff(p2, small(1, 2));
        PointsToSet shared = p1.getPointsToSet();
        int base = interner.size();

        PointsToSet copy = interner.unshare(p1);
        assertSame(copy, p1.getPointsToSet());
        assertFalse(copy.isShared());
        assertEquals(List.of(1, 2), sequence(copy));
        copy.removeIf(o -> o.getIndex() == 1);
        assertEquals(List.of(1, 2), sequence(shared), "the shared set changed");
        assertEquals(base, interner.size(), "the set p2 holds left the table");

        interner.unshare(p2);
        assertEquals(base - 1, interner.size(), "a set no pointer holds stayed in the table");
        assertNull(interner.find(small(1, 2)));
        assertSame(copy, interner.unshare(p1), "an unshared set was copied again");
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
                int k = (i + 1 + random.nextInt(n - 1)) % n;
                PointsToSet referenceDiff;
                PointsToSet diff;
                if (random.nextInt(5) == 0 && pointers[k].getPointsToSet() != null) {
                    // the held set of another pointer, as a new edge propagates it
                    referenceDiff = references[i].addAllDiff(references[k]);
                    diff = sharing.addAllDiff(pointers[i], pointers[k].getPointsToSet());
                } else {
                    int[] picked = pick(random);
                    boolean asLarge = random.nextInt(4) == 0;
                    referenceDiff = references[i].addAllDiff(
                            asLarge ? large(picked) : small(picked));
                    diff = sharing.addAllDiff(pointers[i],
                            asLarge ? large(picked) : small(picked));
                }
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
                    DelegatePointsToSet delegate = (DelegatePointsToSet) held;
                    if (delegate.isLarge() && delegate.holders >= 2) {
                        assertTrue(delegate.isPacked(), at + " pointer " + j);
                    }
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

    @Test
    void largeSetHeldByTwoIsStoredPacked() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        int[] objects = {1, 9, 40, 41, 63};
        interner.addAllDiff(p1, large(objects));
        DelegatePointsToSet first = (DelegatePointsToSet) p1.getPointsToSet();
        assertFalse(first.isPacked(), "a set held by one pointer was packed");
        interner.addAllDiff(p2, large(objects));
        assertSame(first, p2.getPointsToSet());
        assertTrue(first.isPacked());
        assertEquals(List.of(1, 9, 40, 41, 63), sequence(first));
        assertTrue(first.contains(objs[40]));
        assertFalse(first.contains(objs[39]));
        assertSame(first, interner.find(large(objects)));
        assertTrue(first.isPacked(), "a read restored the blocks");
        // p2 changes a copy; the set stays packed for p1
        PointsToSet diff = interner.addAllDiff(p2, large(2, 9));
        assertEquals(List.of(2), sequence(diff));
        assertEquals(List.of(1, 2, 9, 40, 41, 63), sequence(p2.getPointsToSet()));
        assertTrue(first.isPacked());
        // p1 holds it alone now and changes it in place
        diff = interner.addAllDiff(p1, small(3));
        assertSame(first, p1.getPointsToSet());
        assertFalse(first.isPacked());
        assertEquals(List.of(3), sequence(diff));
        assertEquals(List.of(1, 3, 9, 40, 41, 63), sequence(first));
    }

    @Test
    void soleHolderChangesItsSetInPlace() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2));
        PointsToSet sole = p1.getPointsToSet();
        PointsToSet diff = interner.addAllDiff(p1, small(2, 3));
        assertSame(sole, p1.getPointsToSet());
        assertTrue(sole.isShared());
        assertEquals(List.of(3), sequence(diff));
        assertEquals(List.of(1, 2, 3), sequence(sole));
        assertSame(sole, interner.find(small(1, 2, 3)));
        assertNull(interner.find(small(1, 2)));
        // a set held by two pointers is copied
        interner.addAllDiff(p2, small(1, 2, 3));
        assertSame(sole, p2.getPointsToSet());
        interner.addAllDiff(p1, small(4));
        assertNotSame(sole, p1.getPointsToSet());
        assertEquals(List.of(1, 2, 3), sequence(p2.getPointsToSet()));
        assertEquals(List.of(1, 2, 3, 4), sequence(p1.getPointsToSet()));
    }

    @Test
    void soleHolderGivesWayToAnEqualSharedSet() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        interner.addAllDiff(p1, small(1, 2, 3));
        PointsToSet target = p1.getPointsToSet();
        interner.addAllDiff(p2, small(1, 2));
        interner.addAllDiff(p2, small(3));
        assertSame(target, p2.getPointsToSet());
        assertNull(interner.find(small(1, 2)));
        // the table holds the empty set and the one shared set
        assertEquals(2, interner.size());
        // the shared set counts both pointers, so a change of p1 is made on a copy
        interner.addAllDiff(p1, small(4));
        assertSame(target, p2.getPointsToSet());
        assertEquals(List.of(1, 2, 3), sequence(target));
        assertSame(target, interner.find(small(1, 2, 3)));
        assertEquals(List.of(1, 2, 3, 4), sequence(p1.getPointsToSet()));
    }

    @Test
    void soleHolderTurnsItsSmallSetLargeInPlace() {
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, small(1, 2));
        PointsToSet sole = p.getPointsToSet();
        assertFalse(isLarge(sole));
        int[] more = {3, 4, 5, 6, 7, 8, 9, 10};
        PointsToSet reference = small(1, 2);
        PointsToSet referenceDiff = reference.addAllDiff(small(more));
        PointsToSet diff = interner.addAllDiff(p, small(more));
        assertSame(sole, p.getPointsToSet());
        assertTrue(sole.isShared());
        assertTrue(isLarge(reference));
        assertTrue(isLarge(sole));
        assertEquals(sequence(reference), sequence(sole));
        assertEquals(sequence(referenceDiff), sequence(diff));
        assertEquals(isLarge(referenceDiff), isLarge(diff));
        assertSame(sole, interner.find(sole.copy()));
        assertNull(interner.find(small(1, 2)));
        assertEquals(2, interner.size());
    }

    @Test
    void soleHolderAddsALargeSetToItsLargeSetInPlace() {
        Pointer p = TestElements.pointer(1);
        interner.addAllDiff(p, large(1, 2, 3));
        PointsToSet sole = p.getPointsToSet();
        assertTrue(isLarge(sole));
        PointsToSet diff = interner.addAllDiff(p, large(3, 4, 5));
        assertSame(sole, p.getPointsToSet());
        assertTrue(sole.isShared());
        assertTrue(isLarge(sole));
        assertEquals(List.of(1, 2, 3, 4, 5), sequence(sole));
        assertEquals(List.of(4, 5), sequence(diff));
        assertSame(sole, interner.find(large(1, 2, 3, 4, 5)));
        assertNull(interner.find(large(1, 2, 3)));
        assertEquals(2, interner.size());
    }

    @Test
    void countersCountEachChangeByHolderCount() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        Pointer p3 = TestElements.pointer(3);
        Pointer p4 = TestElements.pointer(4);
        Pointer p5 = TestElements.pointer(5);
        // from the empty set (its pin counts as a holder): copy, new set
        interner.addAllDiff(p1, small(1, 2));
        // copy, which gives way to the set p1 holds
        interner.addAllDiff(p2, small(1, 2));
        // two holders: copy, new set
        interner.addAllDiff(p1, small(3));
        // sole holder: in place
        interner.addAllDiff(p1, small(4));
        // two copies from the empty set, both giving way to {1, 2}
        interner.addAllDiff(p3, small(1, 2));
        interner.addAllDiff(p4, small(1, 2));
        // no change: not counted
        interner.addAllDiff(p2, small(1, 2));
        // three holders: copy, new set
        interner.addAllDiff(p2, small(5));
        // from the empty set, then from an unshared set: two copies, new sets
        interner.addAllDiff(p5, small(7));
        interner.unshare(p5);
        interner.addAllDiff(p5, small(8));
        assertEquals(new PointsToSetInterner.Counters(1, 1, 6, 1, 8, 3, 0, 0, 0, 0, 0),
                interner.counters());
    }

    /**
     * The empty set of a pointer that takes a large set equal to a shared
     * set takes that shared set, and returns it as the difference: the same
     * elements, order and form as the copy would give, without a copy.
     */
    @Test
    void emptySetAdoptsAnEqualSharedLargeSet() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        Pointer p3 = TestElements.pointer(3);
        interner.addAllDiff(p1, large(1, 2, 3, 40));
        PointsToSet shared = p1.getPointsToSet();
        PointsToSet reference = factory.make();
        PointsToSet referenceDiff = reference.addAllDiff(large(1, 2, 3, 40));
        int sharedSets = interner.size();
        long copies = interner.counters().copies();

        PointsToSet diff = interner.addAllDiff(p2, large(1, 2, 3, 40));
        assertSame(shared, p2.getPointsToSet());
        assertSame(shared, diff);
        assertEquals(sequence(referenceDiff), sequence(diff));
        assertEquals(isLarge(referenceDiff), isLarge(diff));
        assertEquals(sequence(reference), sequence(p2.getPointsToSet()));
        assertEquals(copies, interner.counters().copies(), "the empty set was copied");
        assertEquals(1, interner.counters().adoptions());
        assertEquals(sharedSets, interner.size());
        // held by p1 and p2, so stored packed
        assertEquals(2, ((DelegatePointsToSet) shared).holders);
        assertTrue(((DelegatePointsToSet) shared).isPacked());
        // a shared set refuses a change, so a caller cannot alter the difference
        assertThrows(IllegalStateException.class, () -> diff.addObject(objs[5]));

        // a large set that no pointer holds, and a small one, are copied as before
        PointsToSet missDiff = interner.addAllDiff(p3, large(1, 2, 3, 41));
        assertFalse(missDiff.isShared());
        assertEquals(List.of(1, 2, 3, 41), sequence(missDiff));
        Pointer p4 = TestElements.pointer(4);
        interner.addAllDiff(p4, small(7));
        assertEquals(copies + 2, interner.counters().copies());
        assertEquals(1, interner.counters().adoptions());
        assertEquals(List.of(1, 2, 3, 40), sequence(p1.getPointsToSet()));
    }

    @Test
    void sharedLargeSetTakesAnEqualSharedResultWithoutACopy() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        Pointer p3 = TestElements.pointer(3);
        Pointer p4 = TestElements.pointer(4);
        interner.addAllDiff(p1, large(1, 2, 3, 40));
        interner.addAllDiff(p2, large(1, 2, 3, 40));
        interner.addAllDiff(p4, large(1, 2, 3, 40));
        PointsToSet before = p1.getPointsToSet();
        assertSame(before, p2.getPointsToSet());
        interner.addAllDiff(p3, large(1, 2, 3, 40, 50));
        PointsToSet target = p3.getPointsToSet();
        int sharedSets = interner.size();
        long copies = interner.counters().copies();

        PointsToSet diff = interner.addAllDiff(p1, large(3, 50));
        assertEquals(copies, interner.counters().copies(), "the held set was copied");
        assertSame(target, p1.getPointsToSet());
        assertEquals(List.of(50), sequence(diff));
        assertTrue(isLarge(diff));
        assertFalse(diff.isShared());
        assertSame(before, p2.getPointsToSet());
        assertEquals(List.of(1, 2, 3, 40), sequence(before));
        assertEquals(sharedSets, interner.size());

        // a probe that finds nothing copies as before (p2 and p4 hold the set)
        PointsToSet missDiff = interner.addAllDiff(p2, large(60));
        assertEquals(copies + 1, interner.counters().copies());
        assertEquals(List.of(60), sequence(missDiff));
        assertTrue(isLarge(missDiff));
        assertEquals(List.of(1, 2, 3, 40, 60), sequence(p2.getPointsToSet()));
        assertSame(before, p4.getPointsToSet());
        assertEquals(List.of(1, 2, 3, 40), sequence(before));
        // p2 and p4 took p1's set from the empty set without a copy
        assertEquals(new PointsToSetInterner.Counters(0, 0, 5, 1, 3, 0, 2, 1, 2, 0, 0),
                interner.counters());
    }

    /**
     * A large set held by two or more that takes a small set finds the
     * result in the table without copying the large set; the difference has
     * the elements, order and form a copy would give.
     */
    @Test
    void sharedLargeSetTakesAnEqualSharedResultOfASmallSetWithoutACopy() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        Pointer p3 = TestElements.pointer(3);
        Pointer p4 = TestElements.pointer(4);
        Pointer p5 = TestElements.pointer(5);
        interner.addAllDiff(p1, large(1, 2, 3, 40));
        interner.addAllDiff(p2, large(1, 2, 3, 40));
        interner.addAllDiff(p4, large(1, 2, 3, 40));
        PointsToSet before = p1.getPointsToSet();
        assertSame(before, p2.getPointsToSet());
        interner.addAllDiff(p3, large(1, 2, 3, 5, 6, 40));
        PointsToSet target = p3.getPointsToSet();
        // the same elements in the small form: not the large result
        interner.addAllDiff(p5, small(1, 2, 3, 40, 60));
        int sharedSets = interner.size();
        long copies = interner.counters().copies();

        // two new objects in one word, one known, in an order a copy keeps
        PointsToSet reference = before.copy();
        PointsToSet referenceDiff = reference.addAllDiff(small(6, 3, 5));
        PointsToSet diff = interner.addAllDiff(p1, small(6, 3, 5));
        assertEquals(copies, interner.counters().copies(), "the held set was copied");
        assertSame(target, p1.getPointsToSet());
        assertEquals(List.of(6, 5), sequence(referenceDiff));
        assertEquals(sequence(referenceDiff), sequence(diff));
        assertEquals(isLarge(referenceDiff), isLarge(diff));
        assertFalse(diff.isShared());
        assertEquals(sequence(reference), sequence(target));
        assertSame(before, p2.getPointsToSet());
        assertEquals(List.of(1, 2, 3, 40), sequence(before));
        assertEquals(sharedSets, interner.size());

        // a singleton whose result the table holds only in the small form,
        // and a probe that finds nothing, both copy as before
        PointsToSet singletonDiff = interner.addAllDiff(p2, small(60));
        assertEquals(copies + 1, interner.counters().copies());
        assertEquals(List.of(60), sequence(singletonDiff));
        assertFalse(isLarge(singletonDiff));
        assertTrue(isLarge(p2.getPointsToSet()));
        assertNotSame(p5.getPointsToSet(), p2.getPointsToSet());
        assertEquals(List.of(1, 2, 3, 40, 60), sequence(p2.getPointsToSet()));
        assertSame(before, p4.getPointsToSet());
        assertEquals(List.of(1, 2, 3, 40), sequence(before));
        PointsToSetInterner.Counters counters = interner.counters();
        assertEquals(2, counters.smallProbes());
        assertEquals(1, counters.smallProbeHits());
        assertEquals(0, counters.probes());
    }

    /**
     * Random sequences of changes on several pointers, against a copying
     * interner kept here: after each step every pointer's set has the same
     * elements, iteration order and form, each difference has the same
     * elements, order and form, and two pointers share a set exactly when
     * they share one in the copying interner. The table starts at two slots,
     * so in-place changes meet its growth and its deletions.
     */
    @Test
    void inPlaceChangeMatchesTheCopyingInterner() {
        long probes = 0;
        long probeHits = 0;
        long adoptions = 0;
        long smallProbes = 0;
        long smallProbeHits = 0;
        for (long seed = 1; seed <= 40; ++seed) {
            Random random = new Random(seed);
            PointsToSetInterner sharing = new PointsToSetInterner(factory, 2);
            CopyingInterner copying = new CopyingInterner();
            int n = 10;
            Pointer[] pointers = new Pointer[n];
            PointsToSet[] copied = new PointsToSet[n];
            for (int i = 0; i < n; ++i) {
                pointers[i] = TestElements.pointer(i);
            }
            for (int step = 0; step < 600; ++step) {
                int i = random.nextInt(n);
                int[] picked = pick(random);
                boolean asLarge = random.nextInt(4) == 0;
                PointsToSet held = copied[i] != null ? copied[i] : factory.make();
                PointsToSet[] next = new PointsToSet[1];
                PointsToSet copyDiff = copying.addAllDiff(held,
                        asLarge ? large(picked) : small(picked), next);
                copied[i] = next[0];
                PointsToSet diff = sharing.addAllDiff(pointers[i],
                        asLarge ? large(picked) : small(picked));
                String at = "seed " + seed + " step " + step;
                assertEquals(sequence(copyDiff), sequence(diff), at);
                // a change that adds nothing returns the shared empty set, whose
                // form differs from an empty large difference; the solver only
                // asks an empty difference whether it is empty
                if (!copyDiff.isEmpty()) {
                    assertEquals(isLarge(copyDiff), isLarge(diff), at);
                }
                for (int j = 0; j < n; ++j) {
                    PointsToSet set = pointers[j].getPointsToSet();
                    if (copied[j] == null) {
                        assertNull(set, at);
                        continue;
                    }
                    assertEquals(sequence(copied[j]), sequence(set), at);
                    assertEquals(isLarge(copied[j]), isLarge(set), at);
                    for (int k = 0; k < n; ++k) {
                        if (copied[k] != null) {
                            assertEquals(copied[j] == copied[k],
                                    set == pointers[k].getPointsToSet(), at);
                        }
                    }
                }
                Set<PointsToSet> distinct = Collections.newSetFromMap(new IdentityHashMap<>());
                for (Pointer p : pointers) {
                    PointsToSet set = p.getPointsToSet();
                    if (set != null && !set.isEmpty()) {
                        distinct.add(set);
                        assertSame(set, sharing.find(set.copy()), at);
                    }
                }
                // the distinct non-empty held sets plus the empty set
                assertEquals(distinct.size() + 1, sharing.size(), at);
            }
            probes += sharing.counters().probes();
            probeHits += sharing.counters().probeHits();
            adoptions += sharing.counters().adoptions();
            smallProbes += sharing.counters().smallProbes();
            smallProbeHits += sharing.counters().smallProbeHits();
        }
        // the sequences take both outcomes of a probe before a copy
        assertTrue(probeHits > 0, "no probe found its result");
        assertTrue(probes > probeHits, "every probe found its result");
        assertTrue(smallProbeHits > 0, "no probe by a small set found its result");
        assertTrue(smallProbes > smallProbeHits, "every probe by a small set found its result");
        assertTrue(adoptions > 0, "no empty set adopted a shared set");
    }

    /**
     * The copy-on-write interner: every change is made on a copy, which is
     * then replaced by the kept set with the same form and sequence.
     */
    private final class CopyingInterner {

        private final List<DelegatePointsToSet> kept = new ArrayList<>();

        private final IdentityHashMap<PointsToSet, Integer> holders = new IdentityHashMap<>();

        /**
         * Applies {@code pts} to a copy of {@code held} and puts the kept set
         * equal to the result into {@code next[0]}.
         *
         * @return the difference
         */
        PointsToSet addAllDiff(PointsToSet held, PointsToSet pts, PointsToSet[] next) {
            DelegatePointsToSet copy = (DelegatePointsToSet) held.copy();
            PointsToSet diff = copy.addAllDiff(pts);
            DelegatePointsToSet result = copy;
            for (DelegatePointsToSet k : kept) {
                if (k.sameSequence(copy)) {
                    result = k;
                    break;
                }
            }
            if (result == copy) {
                kept.add(copy);
            }
            holders.merge(result, 1, Integer::sum);
            if (holders.containsKey(held) && holders.merge(held, -1, Integer::sum) == 0) {
                holders.remove(held);
                kept.removeIf(k -> k == held);
            }
            next[0] = result;
            return diff;
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

    /**
     * A large set held by one pointer alone is packed in place on request:
     * its contents, order and table place stay; a set that is small, held
     * by two or packed already is left alone; a change in place restores it.
     */
    @Test
    void soleHeldLargeSetPacksInPlaceAndAChangeRestoresIt() {
        Pointer p1 = TestElements.pointer(1);
        Pointer p2 = TestElements.pointer(2);
        Pointer p3 = TestElements.pointer(3);
        interner.addAllDiff(p1, large(1, 2, 3, 40));
        interner.addAllDiff(p2, small(5));
        interner.addAllDiff(p3, large(7, 8, 9, 41));
        interner.addAllDiff(TestElements.pointer(4), large(7, 8, 9, 41));
        PointsToSet sole = p1.getPointsToSet();
        assertTrue(interner.holdsUnpackedSole(p1));
        assertFalse(interner.holdsUnpackedSole(p2), "small");
        assertFalse(interner.holdsUnpackedSole(p3), "held by two");
        assertFalse(interner.packSoleHeld(p2));
        assertFalse(interner.packSoleHeld(p3));
        assertEquals(0, interner.solePacks());

        assertTrue(interner.packSoleHeld(p1));
        assertSame(sole, p1.getPointsToSet());
        assertTrue(((DelegatePointsToSet) sole).isPacked());
        assertEquals(1, ((DelegatePointsToSet) sole).holders);
        assertEquals(List.of(1, 2, 3, 40), sequence(sole));
        assertTrue(isLarge(sole));
        assertSame(sole, interner.find(large(1, 2, 3, 40)));
        assertFalse(interner.holdsUnpackedSole(p1), "packed already");
        assertFalse(interner.packSoleHeld(p1));
        assertEquals(1, interner.solePacks());

        PointsToSet diff = interner.addAllDiff(p1, large(3, 50));
        assertEquals(List.of(50), sequence(diff));
        assertEquals(List.of(1, 2, 3, 40, 50), sequence(p1.getPointsToSet()));
        assertEquals(0, interner.packedSoleWrites(), "not counted by default");
        assertTrue(interner.holdsUnpackedSole(p1));

        PointsToSetInterner counting = new PointsToSetInterner(factory, true);
        Pointer q = TestElements.pointer(5);
        counting.addAllDiff(q, large(1, 2, 3, 40));
        counting.addAllDiff(q, large(41));
        assertEquals(0, counting.packedSoleWrites(), "an unpacked set");
        assertTrue(counting.packSoleHeld(q));
        counting.addAllDiff(q, large(42));
        assertEquals(1, counting.packedSoleWrites());
        assertEquals(List.of(1, 2, 3, 40, 41, 42), sequence(q.getPointsToSet()));
    }

    /**
     * Random writes with and without packing sole held sets between them
     * give the same sets, differences, forms, table sizes and counters.
     */
    @Test
    void packingSoleHeldSetsKeepsEveryResult() {
        for (long seed = 1; seed <= 20; ++seed) {
            Random random = new Random(seed);
            PointsToSetInterner plain = new PointsToSetInterner(factory);
            PointsToSetInterner packing = new PointsToSetInterner(factory);
            int n = 12;
            Pointer[] plainPointers = new Pointer[n];
            Pointer[] packingPointers = new Pointer[n];
            for (int i = 0; i < n; ++i) {
                plainPointers[i] = TestElements.pointer(i);
                packingPointers[i] = TestElements.pointer(i);
            }
            for (int step = 0; step < 300; ++step) {
                String at = "seed " + seed + " step " + step;
                for (int i = 0; i < n; ++i) {
                    if (random.nextInt(3) == 0 && packingPointers[i].getPointsToSet() != null) {
                        packing.packSoleHeld(packingPointers[i]);
                    }
                }
                int i = random.nextInt(n);
                int[] picked = pick(random);
                PointsToSet delta = random.nextBoolean() || picked.length > 4
                        ? large(picked) : small(picked);
                PointsToSet plainDiff = plain.addAllDiff(plainPointers[i], delta);
                PointsToSet packingDiff = packing.addAllDiff(packingPointers[i], delta.copy());
                assertEquals(sequence(plainDiff), sequence(packingDiff), at);
                assertEquals(isLarge(plainDiff), isLarge(packingDiff), at);
                PointsToSet plainSet = plainPointers[i].getPointsToSet();
                PointsToSet packingSet = packingPointers[i].getPointsToSet();
                assertEquals(sequence(plainSet), sequence(packingSet), at);
                assertEquals(isLarge(plainSet), isLarge(packingSet), at);
                assertEquals(plain.size(), packing.size(), at);
            }
            assertEquals(plain.counters(), packing.counters(), "seed " + seed);
            assertTrue(packing.solePacks() > 0, "seed " + seed);
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
