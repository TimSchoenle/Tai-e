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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks {@link WorkList} against the work list that keeps every pending
 * delta as a copied points-to set: random sequences of adds, merges and
 * polls must poll the same pointers with sets of the same objects, the same
 * iteration order and the same small or large form.
 */
class WorkListModelTest {

    /**
     * The objects and pointers of an analysed program. Public with a
     * no-argument constructor: the analysis loads it by name.
     */
    public static class Capture implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            csManager = solver.getCSManager();
            Set<CSObj> seen = Sets.newLinkedSet();
            csManager.pointers().forEach(p -> {
                pointers.add(p);
                seen.addAll(p.getObjects());
            });
            objects.addAll(seen);
        }
    }

    private static CSManager csManager;

    private static final List<Pointer> pointers = new ArrayList<>();

    private static final List<CSObj> objects = new ArrayList<>();

    /** The two objects of the lowest indexes, kept out of the random sets for the form probe. */
    private static CSObj lowest;

    private static CSObj secondLowest;

    private static PointsToSetFactory factory;

    private static FarIndexer farIndexer;

    /** A factory whose indexer spreads the objects over several areas. */
    private static PointsToSetFactory farFactory;

    @BeforeAll
    static void analyse() {
        pointers.clear();
        objects.clear();
        Main.main("-cp", "src/test/resources/pta/fan", "-m", "FanOut",
                "-a", "pta=only-app:true;implicit-entries:false;cs:2-obj;plugins:["
                        + Capture.class.getName() + "]");
        assertNotNull(csManager);
        Indexer<CSObj> indexer = csManager.getObjectIndexer();
        objects.sort(Comparator.comparingInt(indexer::getIndex));
        // two objects for the form probe, and more than a small set holds
        assertTrue(objects.size() >= 12, "too few objects: " + objects.size());
        assertTrue(pointers.size() >= 10, "too few pointers: " + pointers.size());
        lowest = objects.remove(0);
        secondLowest = objects.remove(0);
        factory = new PointsToSetFactory(indexer);
        farIndexer = new FarIndexer();
        farFactory = new PointsToSetFactory(farIndexer);
    }

    @Test
    void randomSequencesMatchTheCopyingWorkList() {
        assertSequencesMatch(factory, true, 12);
    }

    @Test
    void randomSequencesWithoutPackingMatchTheCopyingWorkList() {
        assertSequencesMatch(factory, false, 12);
    }

    /**
     * Every pointer of the program: the ring and the index array grow
     * while pointers are pending, and the order survives the growth.
     */
    @Test
    void randomSequencesOverAllPointersMatchTheCopyingWorkList() {
        assertTrue(pointers.size() > 40, "too few pointers: " + pointers.size());
        int peak = assertSequencesMatch(factory, true, pointers.size());
        // more pending than the initial ring holds, and pointer indexes past the initial index array
        assertTrue(peak > 16, "peak: " + peak);
        assertTrue(pointers.stream().anyMatch(p -> p.getIndex() >= 16));
    }

    /**
     * A scripted run: the poll order is the order of first pending
     * insertion, a merge keeps the place, a pointer polled and added again
     * goes last; the counters count each step.
     */
    @Test
    void scriptedRunPollsInFirstInsertionOrderAndCounts() {
        Pointer a = pointers.get(0);
        Pointer b = pointers.get(1);
        Pointer c = pointers.get(2);
        PointsToSet small = factory.make();
        small.addObject(objects.get(0));
        PointsToSet large = factory.make();
        objects.forEach(large::addObject);
        WorkList workList = new WorkList(factory, true);
        workList.addEntry(c, small);
        workList.addEntry(a, large);
        workList.addEntry(b, small);
        workList.addEntry(c, large);
        workList.addEntry(a, small);
        assertEquals(3, workList.pendingPointers());
        assertEquals(3, workList.newEntries());
        assertEquals(2, workList.mergedEntries());
        assertEquals(1, workList.packs());
        assertEquals(1, workList.unpacks());
        assertSame(c, workList.pollPointer());
        assertEquals(order(large), order(workList.takePolledDelta()));
        workList.addEntry(c, small);
        assertSame(a, workList.pollPointer());
        assertEquals(order(large), order(workList.takePolledDelta()));
        workList.addEntry(b, large);
        assertSame(b, workList.pollPointer());
        assertEquals(order(large), order(workList.takePolledDelta()));
        assertSame(c, workList.pollPointer());
        assertEquals(List.of(objects.get(0)), order(workList.takePolledDelta()));
        assertTrue(workList.isEmpty());
        assertEquals(0, workList.pendingPointers());
        assertEquals(3, workList.pendingPeak());
        assertEquals(4, workList.newEntries());
        assertEquals(3, workList.mergedEntries());
        assertEquals(1, workList.packs());
        assertEquals(1, workList.unpacks());
        assertEquals("pending_pointers=0 pending_peak=3 new_entries=4"
                + " merged_entries=3 packs=1 unpacks=1", workList.countersLine());
    }

    @Test
    void unpackedRunNeitherPacksNorUnpacks() {
        PointsToSet large = factory.make();
        objects.forEach(large::addObject);
        WorkList workList = new WorkList(factory, false);
        workList.addEntry(pointers.get(0), large);
        workList.addEntry(pointers.get(1), large);
        workList.pollPointer();
        workList.takePolledDelta();
        assertEquals(0, workList.packs());
        assertEquals(0, workList.unpacks());
        WorkList packing = new WorkList(factory, true);
        packing.addEntry(pointers.get(0), large);
        packing.addEntry(pointers.get(1), large);
        packing.pollPointer();
        packing.takePolledDelta();
        assertEquals(2, packing.packs());
        assertEquals(1, packing.unpacks());
    }

    @Test
    void emptyPollsAndDoubleTakesThrow() {
        WorkList workList = new WorkList(factory, true);
        assertThrows(NoSuchElementException.class, workList::pollPointer);
        assertThrows(NoSuchElementException.class, workList::pollCallEdge);
        assertThrows(IllegalStateException.class, workList::takePolledDelta);
        PointsToSet small = factory.make();
        small.addObject(objects.get(0));
        workList.addEntry(pointers.get(0), small);
        workList.pollPointer();
        workList.takePolledDelta();
        assertThrows(IllegalStateException.class, workList::takePolledDelta);
        workList.addEntry(pointers.get(0), small);
        workList.addEntry(pointers.get(1), small);
        workList.pollPointer();
        assertThrows(IllegalStateException.class, workList::pollPointer);
    }

    /**
     * The same sequences with the objects indexed far apart: a large delta
     * then spans several areas and blocks, near the largest index too.
     */
    @Test
    void multiAreaSequencesMatchTheCopyingWorkList() {
        assertSequencesMatch(farFactory, true, 12);
        PointsToSet all = farFactory.make();
        objects.forEach(all::addObject);
        long[] words = farFactory.toPackedLarge(all);
        assertNotNull(words);
        // one header per block and one word per non-zero word
        Set<Integer> blocks = Sets.newSet();
        Set<Integer> nonZeroWords = Sets.newSet();
        objects.forEach(o -> {
            blocks.add(farIndexer.getIndex(o) >>> 9);
            nonZeroWords.add(farIndexer.getIndex(o) >>> 6);
        });
        assertTrue(blocks.size() > objects.size() / 2, "blocks: " + blocks.size());
        assertEquals(blocks.size() + nonZeroWords.size(), words.length);
        assertEquals(order(all), order(farFactory.ofPackedLarge(words)));
    }

    /**
     * @return the largest number of pointers pending at once over all seeds.
     */
    private static int assertSequencesMatch(
            PointsToSetFactory factory, boolean packLarge, int pointerRange) {
        int maxPeak = 0;
        for (int seed = 0; seed < 300; ++seed) {
            Random random = new Random(seed);
            WorkList workList = new WorkList(factory, packLarge);
            CopyingWorkList model = new CopyingWorkList();
            int steps = 50 + random.nextInt(400);
            for (int step = 0; step < steps; ++step) {
                if (random.nextInt(10) < 7) {
                    Pointer pointer = pointers.get(
                            random.nextInt(Math.min(pointers.size(), pointerRange)));
                    PointsToSet delta = randomSet(factory, random);
                    workList.addEntry(pointer, delta);
                    model.addEntry(pointer, delta);
                    if (random.nextBoolean()) {
                        // the caller may change its set after adding it
                        delta.addObject(objects.get(random.nextInt(objects.size())));
                    }
                } else if (!model.isEmpty()) {
                    assertSamePoll(model, workList, seed + "/" + step);
                }
                assertEquals(model.isEmpty(), workList.isEmpty(), seed + "/" + step);
            }
            while (!model.isEmpty()) {
                assertSamePoll(model, workList, seed + "/drain");
            }
            assertTrue(workList.isEmpty());
            assertEquals(model.newEntries, workList.newEntries(), "seed " + seed);
            assertEquals(model.mergedEntries, workList.mergedEntries(), "seed " + seed);
            assertEquals(model.peak, workList.pendingPeak(), "seed " + seed);
            if (!packLarge) {
                assertEquals(0, workList.packs() + workList.unpacks(), "seed " + seed);
            }
            maxPeak = Math.max(maxPeak, workList.pendingPeak());
        }
        return maxPeak;
    }

    @Test
    void onlyLargeSetsArePacked() {
        Random random = new Random(1);
        int packed = 0;
        for (int i = 0; i < 200; ++i) {
            PointsToSet set = randomSet(factory, random);
            List<CSObj> before = order(set);
            long[] words = factory.toPackedLarge(set);
            assertEquals(words != null, formProbe(set).get(0) == lowest, "set " + before);
            if (words != null) {
                ++packed;
                assertEquals(before, order(factory.ofPackedLarge(words)));
            }
        }
        assertTrue(packed > 50, "packed sets: " + packed);
    }

    private static void assertSamePoll(CopyingWorkList model, WorkList workList, String at) {
        Map.Entry<Pointer, PointsToSet> expected = model.poll();
        Pointer actualPointer = workList.pollPointer();
        PointsToSet actualDelta = workList.takePolledDelta();
        assertSame(expected.getKey(), actualPointer, at);
        assertEquals(order(expected.getValue()), order(actualDelta), at);
        assertEquals(formProbe(expected.getValue()), formProbe(actualDelta), at);
        assertEquals(model.entries.size(), workList.pendingPointers(), at);
    }

    private static List<CSObj> order(PointsToSet pts) {
        List<CSObj> order = new ArrayList<>();
        pts.forEach(order::add);
        return order;
    }

    /**
     * Adds the two lowest objects to a copy: a large set sorts them first,
     * a small set appends them in the order they were added.
     */
    private static List<CSObj> formProbe(PointsToSet pts) {
        PointsToSet copy = pts.copy();
        copy.addObject(secondLowest);
        copy.addObject(lowest);
        return order(copy);
    }

    private static PointsToSet randomSet(PointsToSetFactory factory, Random random) {
        PointsToSet set = factory.make();
        int kind = random.nextInt(5);
        if (kind == 0 || kind == 1) {
            // small: at most six objects stay small after the form probe
            int count = random.nextInt(7);
            for (int i = 0; i < count; ++i) {
                set.addObject(objects.get(random.nextInt(objects.size())));
            }
            return set;
        }
        // large: more objects than a small set holds, then some removed
        List<CSObj> shuffled = new ArrayList<>(objects);
        Collections.shuffle(shuffled, random);
        shuffled.forEach(set::addObject);
        if (kind == 4) {
            // large form with few or no objects, as a difference set can be
            Set<CSObj> kept = Sets.newSet(shuffled.subList(0, random.nextInt(4)));
            set.removeIf(o -> !kept.contains(o));
        } else {
            set.removeIf(o -> random.nextInt(10) < 3);
        }
        return set;
    }

    /**
     * Indexes the two form probe objects 0 and 1, and the other objects in
     * turn far apart in the first areas, an area apart, and just below the
     * largest index.
     */
    private static final class FarIndexer implements Indexer<CSObj> {

        private final Map<CSObj, Integer> indexes = Maps.newMap();

        private final Map<Integer, CSObj> objectsByIndex = Maps.newMap();

        FarIndexer() {
            assertTrue(objects.size() < 20_000, "too many objects: " + objects.size());
            put(lowest, 0);
            put(secondLowest, 1);
            for (int i = 0; i < objects.size(); ++i) {
                int index = switch (i % 3) {
                    case 0 -> 1024 + i * 70_001;
                    case 1 -> (i + 2) << 16;
                    default -> Integer.MAX_VALUE - 1 - i * 1024;
                };
                put(objects.get(i), index);
            }
        }

        private void put(CSObj obj, int index) {
            assertTrue(objectsByIndex.put(index, obj) == null, "index used twice: " + index);
            indexes.put(obj, index);
        }

        @Override
        public int getIndex(CSObj o) {
            return indexes.get(o);
        }

        @Override
        public CSObj getObject(int index) {
            return objectsByIndex.get(index);
        }
    }

    /** The work list as it was: every pending delta a copied points-to set. */
    private static final class CopyingWorkList {

        private final Map<Pointer, PointsToSet> entries = Maps.newLinkedHashMap();

        private long newEntries;

        private long mergedEntries;

        private int peak;

        void addEntry(Pointer pointer, PointsToSet pointsToSet) {
            PointsToSet set = entries.get(pointer);
            if (set != null) {
                set.addAll(pointsToSet);
                ++mergedEntries;
            } else {
                entries.put(pointer, pointsToSet.copy());
                ++newEntries;
                peak = Math.max(peak, entries.size());
            }
        }

        Map.Entry<Pointer, PointsToSet> poll() {
            var it = entries.entrySet().iterator();
            var e = it.next();
            it.remove();
            return e;
        }

        boolean isEmpty() {
            return entries.isEmpty();
        }
    }
}
