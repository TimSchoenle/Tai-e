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
import pascal.taie.analysis.pta.pts.DelegatePointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.HybridBitSet;
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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
        long[] words = factory.toPackedLarge(large);
        assertNotNull(words);
        assertEquals("pending_pointers=0 pending_peak=3 new_entries=4"
                + " merged_entries=3 packs=1 unpacks=1 shared_entries=0 shared_copies=0"
                + " packed_by_reference=0 packed_copy_bytes=" + words.length * Long.BYTES
                + " packed_reference_bytes=0",
                workList.countersLine());
    }

    /**
     * A large set stored packed is taken by reference, not packed again;
     * its words are never written: neither a merge into one holder, nor a
     * change of the caller's set, nor a change of a polled delta alters the
     * delta of another holder or a later restore of the same words.
     */
    @Test
    void packedSetIsTakenByReferenceAndItsWordsAreNeverWritten() {
        Pointer a = pointers.get(0);
        Pointer b = pointers.get(1);
        Pointer c = pointers.get(2);
        PointsToSet missing = factory.make();
        missing.addObject(objects.get(1));
        PointsToSet source = factory.make();
        objects.forEach(source::addObject);
        source.removeIf(o -> o == objects.get(1));
        packStored(source);
        List<CSObj> before = order(source);
        List<CSObj> formBefore = formProbe(source);
        long[] copiedWords = factory.toPackedLarge(source);
        assertNotNull(copiedWords);
        var snapshot = factory.packedLargeSnapshot(source);
        assertNotNull(snapshot);
        assertEquals(copiedWords.length, snapshot.length());
        WorkList workList = new WorkList(factory, true);
        workList.addEntry(a, source);
        workList.addFanOutEntry(b, source);
        workList.addFanOutEntry(c, source);
        workList.endFanOut();
        // c shares the snapshot b stored in the same fan-out
        assertEquals(2, workList.packs());
        assertEquals(2, workList.packedByReference());
        assertEquals(1, workList.sharedEntries());
        assertEquals(0, workList.packedCopyBytes());
        assertEquals(2L * copiedWords.length * Long.BYTES, workList.packedReferenceBytes());
        // a merge restores the delta of one holder and changes the restored set
        workList.addEntry(a, missing);
        assertEquals(1, workList.unpacks());
        // the caller's set restores its blocks to change
        source.removeIf(o -> o == objects.get(2));
        assertSame(a, workList.pollPointer());
        PointsToSet polled = workList.takePolledDelta();
        assertEquals(objects, order(polled));
        polled.removeIf(o -> true);
        assertSame(b, workList.pollPointer());
        PointsToSet polledB = workList.takePolledDelta();
        assertEquals(before, order(polledB));
        assertEquals(formBefore, formProbe(polledB));
        polledB.removeIf(o -> true);
        assertSame(c, workList.pollPointer());
        assertEquals(before, order(workList.takePolledDelta()));
        assertEquals(3, workList.unpacks());
        assertEquals(before, order(factory.ofPackedLarge(snapshot)));
        assertEquals(before, order(factory.ofPackedLarge(copiedWords)));
        assertFalse(order(source).contains(objects.get(2)));
    }

    /**
     * One fan-out stores each set once: the large set is packed once for
     * two pointers, the small set copied once for two; a merge into one
     * holder of the small set leaves the other holder's delta unchanged.
     */
    @Test
    void fanOutStoresEachSetOnceAndCopiesOnWrite() {
        Pointer a = pointers.get(0);
        Pointer b = pointers.get(1);
        Pointer c = pointers.get(2);
        Pointer d = pointers.get(3);
        PointsToSet small = factory.make();
        small.addObject(objects.get(0));
        PointsToSet other = factory.make();
        other.addObject(objects.get(1));
        PointsToSet large = factory.make();
        objects.forEach(large::addObject);
        WorkList workList = new WorkList(factory, true);
        workList.addFanOutEntry(a, large);
        workList.addFanOutEntry(c, small);
        workList.addFanOutEntry(b, large);
        workList.addFanOutEntry(d, small);
        workList.endFanOut();
        // the caller may change its sets after the fan-out
        small.addObject(objects.get(2));
        large.removeIf(o -> o == objects.get(3));
        assertEquals(4, workList.newEntries());
        assertEquals(1, workList.packs());
        assertEquals(2, workList.sharedEntries());
        workList.addEntry(c, other);
        workList.addEntry(a, other);
        assertEquals(1, workList.sharedCopies());
        assertEquals(1, workList.unpacks());
        assertSame(a, workList.pollPointer());
        assertEquals(objects, order(workList.takePolledDelta()));
        assertSame(c, workList.pollPointer());
        assertEquals(List.of(objects.get(0), objects.get(1)), order(workList.takePolledDelta()));
        assertSame(b, workList.pollPointer());
        assertEquals(objects, order(workList.takePolledDelta()));
        assertSame(d, workList.pollPointer());
        assertEquals(List.of(objects.get(0)), order(workList.takePolledDelta()));
        assertEquals(2, workList.unpacks());
    }

    /**
     * A set merged in place into its first holder before a second pointer
     * of the fan-out receives the same source is not reused, and a polled
     * pointer ends the reuse.
     */
    @Test
    void fanOutDoesNotReuseASetChangedInPlace() {
        Pointer a = pointers.get(0);
        Pointer b = pointers.get(1);
        Pointer c = pointers.get(2);
        PointsToSet small = factory.make();
        small.addObject(objects.get(0));
        PointsToSet other = factory.make();
        other.addObject(objects.get(1));
        WorkList workList = new WorkList(factory, false);
        workList.addFanOutEntry(a, small);
        workList.addEntry(a, other);
        workList.addFanOutEntry(b, small);
        workList.endFanOut();
        assertEquals(0, workList.sharedEntries());
        assertSame(a, workList.pollPointer());
        assertEquals(List.of(objects.get(0), objects.get(1)), order(workList.takePolledDelta()));
        assertSame(b, workList.pollPointer());
        assertEquals(List.of(objects.get(0)), order(workList.takePolledDelta()));
        workList.addFanOutEntry(a, small);
        assertSame(a, workList.pollPointer());
        PointsToSet polled = workList.takePolledDelta();
        workList.addFanOutEntry(c, small);
        workList.addEntry(c, other);
        workList.endFanOut();
        assertEquals(0, workList.sharedEntries());
        assertEquals(List.of(objects.get(0)), order(polled));
        assertSame(c, workList.pollPointer());
        assertEquals(List.of(objects.get(0), objects.get(1)), order(workList.takePolledDelta()));
    }

    @Test
    void randomFanOutsMatchTheCopyingWorkList() {
        assertFanOutsMatch(factory, true);
    }

    @Test
    void randomFanOutsWithoutPackingMatchTheCopyingWorkList() {
        assertFanOutsMatch(factory, false);
    }

    /**
     * Random fan-outs of a few sets to random pointers, with plain entries
     * among them (as a transfer that adds work does), polls between the
     * fan-outs and the callers' sets changed after each fan-out.
     */
    private static void assertFanOutsMatch(PointsToSetFactory factory, boolean packLarge) {
        long shared = 0;
        long copies = 0;
        for (int seed = 0; seed < 300; ++seed) {
            Random random = new Random(seed);
            WorkList workList = new WorkList(factory, packLarge);
            CopyingWorkList model = new CopyingWorkList();
            int range = Math.min(pointers.size(), 4 + random.nextInt(40));
            int steps = 20 + random.nextInt(120);
            for (int step = 0; step < steps; ++step) {
                if (random.nextInt(10) < 6) {
                    List<PointsToSet> sources = new ArrayList<>();
                    // up to more sources than one fan-out keeps for reuse
                    int sourceCount = 1 + random.nextInt(10);
                    for (int i = 0; i < sourceCount; ++i) {
                        sources.add(randomSet(factory, random));
                    }
                    int targets = 1 + random.nextInt(12);
                    for (int t = 0; t < targets; ++t) {
                        Pointer pointer = pointers.get(random.nextInt(range));
                        if (random.nextInt(8) == 0) {
                            PointsToSet extra = randomSet(factory, random);
                            workList.addEntry(pointer, extra);
                            model.addEntry(pointer, extra);
                        } else {
                            PointsToSet source = sources.get(random.nextInt(sourceCount));
                            workList.addFanOutEntry(pointer, source);
                            model.addEntry(pointer, source);
                        }
                    }
                    workList.endFanOut();
                    for (PointsToSet source : sources) {
                        if (random.nextBoolean()) {
                            source.addObject(objects.get(random.nextInt(objects.size())));
                        }
                    }
                } else {
                    int polls = random.nextInt(4);
                    for (int i = 0; i < polls && !model.isEmpty(); ++i) {
                        assertSamePoll(model, workList, seed + "/" + step);
                    }
                }
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
            shared += workList.sharedEntries();
            copies += workList.sharedCopies();
        }
        assertTrue(shared > 1000, "shared entries: " + shared);
        assertTrue(copies > 100, "shared copies: " + copies);
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
        long byReference = 0;
        long copied = 0;
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
            byReference += workList.packedByReference();
            copied += workList.packs() - workList.packedByReference();
        }
        if (packLarge) {
            // both kinds of packs: packed sets taken by reference, others copied
            assertTrue(byReference > 100, "packs by reference: " + byReference);
            assertTrue(copied > 100, "packs by copy: " + copied);
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
        if (random.nextInt(3) == 0) {
            // stored packed, as a shared set is
            packStored(set);
        }
        return set;
    }

    /**
     * Stores a large set in its packed form, as a points-to set interner
     * does with a set it shares.
     */
    private static void packStored(PointsToSet set) {
        HybridBitSet<?> hybrid = (HybridBitSet<?>) ((DelegatePointsToSet) set).set;
        hybrid.packLarge();
        assertTrue(hybrid.isPackedLarge());
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
