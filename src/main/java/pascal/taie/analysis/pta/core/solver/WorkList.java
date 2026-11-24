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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * Represents work list in pointer analysis.
 * <p>
 * Call edges are polled before pointers. Pointers are polled in the order
 * of their first pending insertion: a pointer that receives a delta while
 * it is pending keeps its place, and the delta is merged into the pending
 * one. The pending pointers are held in a ring (insertion number
 * {@code seq} at slot {@code seq & (capacity - 1)}); a side array by
 * pointer index keeps each pointer's last insertion number. A pointer is
 * pending exactly when the ring slot of its recorded number holds it,
 * since a polled slot is cleared. This needs pointer indexes that are
 * unique among the pointers added to one work list.
 * <p>
 * A pending delta is held either as a {@link PointsToSet} or, when packing
 * is on and it was a large set on arrival, as the packed words of
 * {@link PointsToSetFactory#toPackedLarge}: a large delta usually holds few
 * bits per bit set block, and many deltas can wait at the same time. A
 * packed delta that receives more objects is restored to a set, so merging
 * works on sets as before.
 */
final class WorkList {

    private static final int INITIAL_CAPACITY = 16;

    /**
     * The largest ring capacity, a power of two.
     */
    private static final int MAX_CAPACITY = 1 << 30;

    /**
     * Call edges to be processed.
     */
    private final Queue<Edge<CSCallSite, CSMethod>> callEdges = new ArrayDeque<>();

    private final PointsToSetFactory ptsFactory;

    private final boolean packLarge;

    /**
     * Pending pointers by ring slot; null in a free slot.
     */
    private @Nullable Pointer[] ringPointers = new Pointer[INITIAL_CAPACITY];

    /**
     * Pending deltas by ring slot: a {@link PointsToSet} or packed words.
     */
    private @Nullable Object[] ringDeltas = new Object[INITIAL_CAPACITY];

    /**
     * Insertion number of the oldest pending pointer.
     */
    private int headSeq;

    /**
     * Number of pending pointers.
     */
    private int size;

    /**
     * Insertion number of the last insertion of each pointer, by pointer
     * index; meaningful only while the pointer is pending.
     */
    private int[] seqByIndex = new int[INITIAL_CAPACITY];

    /**
     * The delta of the pointer returned by the last {@link #pollPointer()},
     * until {@link #takePolledDelta()} hands it over.
     */
    private @Nullable PointsToSet polledDelta;

    private int pendingPeak;

    private long newEntries;

    private long mergedEntries;

    private long packs;

    private long unpacks;

    /**
     * @param ptsFactory the factory of the pending sets
     * @param packLarge  whether a pending delta that is a large set on
     *                   arrival is held as packed words
     */
    WorkList(PointsToSetFactory ptsFactory, boolean packLarge) {
        this.ptsFactory = ptsFactory;
        this.packLarge = packLarge;
    }

    void addEntry(Pointer pointer, PointsToSet pointsToSet) {
        int index = pointer.getIndex();
        if (index < seqByIndex.length) {
            int slot = seqByIndex[index] & (ringPointers.length - 1);
            if (ringPointers[slot] == pointer) {
                merge(slot, pointsToSet);
                return;
            }
        }
        if (size == ringPointers.length) {
            growRing();
        }
        if (index >= seqByIndex.length) {
            growIndex(index);
        }
        int seq = headSeq + size;
        int slot = seq & (ringPointers.length - 1);
        ringPointers[slot] = pointer;
        ringDeltas[slot] = newDelta(pointsToSet);
        seqByIndex[index] = seq;
        ++size;
        ++newEntries;
        if (size > pendingPeak) {
            pendingPeak = size;
        }
    }

    private void merge(int slot, PointsToSet pointsToSet) {
        Object pending = ringDeltas[slot];
        if (pending instanceof PointsToSet set) {
            set.addAll(pointsToSet);
        } else {
            PointsToSet set = ptsFactory.ofPackedLarge((long[]) pending);
            ++unpacks;
            set.addAll(pointsToSet);
            ringDeltas[slot] = set;
        }
        ++mergedEntries;
    }

    private Object newDelta(PointsToSet pointsToSet) {
        if (packLarge) {
            long[] packed = ptsFactory.toPackedLarge(pointsToSet);
            if (packed != null) {
                ++packs;
                return packed;
            }
        }
        return pointsToSet.copy();
    }

    /**
     * Doubles the ring. A pending insertion number keeps its meaning: the
     * pending numbers are consecutive and fewer than the old capacity, so
     * they map to distinct slots of the new ring.
     */
    private void growRing() {
        int oldCapacity = ringPointers.length;
        if (oldCapacity == MAX_CAPACITY) {
            throw new IllegalStateException("work list holds too many pointers");
        }
        int oldMask = oldCapacity - 1;
        int newMask = oldCapacity * 2 - 1;
        Pointer[] newPointers = new Pointer[oldCapacity * 2];
        Object[] newDeltas = new Object[oldCapacity * 2];
        for (int i = 0; i < size; ++i) {
            int seq = headSeq + i;
            newPointers[seq & newMask] = ringPointers[seq & oldMask];
            newDeltas[seq & newMask] = ringDeltas[seq & oldMask];
        }
        ringPointers = newPointers;
        ringDeltas = newDeltas;
    }

    private void growIndex(int index) {
        int length = seqByIndex.length;
        int grown = length + (length >> 1);
        int newLength = grown > index ? grown : index + 1;
        seqByIndex = Arrays.copyOf(seqByIndex, newLength);
    }

    void addEntry(Edge<CSCallSite, CSMethod> edge) {
        callEdges.add(edge);
    }

    boolean hasCallEdge() {
        return !callEdges.isEmpty();
    }

    /**
     * Polls a call edge. For correctness, any call edges in the work list
     * must be processed prior to the pointers: the caller polls pointers
     * only while {@link #hasCallEdge()} is false.
     */
    Edge<CSCallSite, CSMethod> pollCallEdge() {
        Edge<CSCallSite, CSMethod> edge = callEdges.poll();
        if (edge == null) {
            throw new NoSuchElementException();
        }
        return edge;
    }

    /**
     * Polls the oldest pending pointer; its delta follows by
     * {@link #takePolledDelta()}.
     */
    Pointer pollPointer() {
        if (size == 0) {
            throw new NoSuchElementException();
        }
        if (polledDelta != null) {
            throw new IllegalStateException("polled pointer delta not taken");
        }
        int slot = headSeq & (ringPointers.length - 1);
        Pointer pointer = ringPointers[slot];
        Object pending = ringDeltas[slot];
        ringPointers[slot] = null;
        ringDeltas[slot] = null;
        ++headSeq;
        --size;
        if (pending instanceof PointsToSet set) {
            polledDelta = set;
        } else {
            polledDelta = ptsFactory.ofPackedLarge((long[]) pending);
            ++unpacks;
        }
        return pointer;
    }

    /**
     * @return the delta of the pointer returned by the last
     * {@link #pollPointer()}; it can be taken once.
     */
    PointsToSet takePolledDelta() {
        PointsToSet delta = polledDelta;
        if (delta == null) {
            throw new IllegalStateException("no polled pointer delta");
        }
        polledDelta = null;
        return delta;
    }

    boolean isEmpty() {
        return size == 0 && callEdges.isEmpty();
    }

    /**
     * @return the number of pending pointer entries.
     */
    int pointerEntryCount() {
        return size;
    }

    /**
     * @return the number of pending call edges.
     */
    int callEdgeCount() {
        return callEdges.size();
    }

    int pendingPointers() {
        return size;
    }

    int pendingPeak() {
        return pendingPeak;
    }

    long newEntries() {
        return newEntries;
    }

    long mergedEntries() {
        return mergedEntries;
    }

    long packs() {
        return packs;
    }

    long unpacks() {
        return unpacks;
    }

    /**
     * @return the counters of the pointer entries, for the log.
     */
    String countersLine() {
        return "pending_pointers=" + size
                + " pending_peak=" + pendingPeak
                + " new_entries=" + newEntries
                + " merged_entries=" + mergedEntries
                + " packs=" + packs
                + " unpacks=" + unpacks;
    }
}
