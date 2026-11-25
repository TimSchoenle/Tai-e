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
import pascal.taie.util.collection.SparseBitSet;

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
 * works on sets as before. A large set that is stored packed already (as a
 * set shared through a points-to set interner is) is not packed again: the
 * delta holds a {@link SparseBitSet.PackedSnapshot} of its packed words by
 * reference, which a merge or poll restores to the same set the copied words
 * would give.
 * <p>
 * The entries of one propagation's fan-out ({@link #addFanOutEntry}, up
 * to {@link #endFanOut()}) share the stored delta of a set they receive by
 * identity: the set is copied, or packed, once for the new entries of the
 * fan-out instead of once per entry. Packed words are never changed
 * (restoring them copies them); a shared set is flagged in every slot that
 * holds it and copied on its first merge there. A delta handed out by
 * {@link #takePolledDelta()} may thus be the pending delta of other
 * pointers: the caller only reads it.
 */
final class WorkList {

    private static final int INITIAL_CAPACITY = 16;

    /**
     * The most distinct sets of one fan-out whose stored deltas are kept
     * for reuse; the entries for further sets are stored as before.
     */
    private static final int FAN_OUT_SOURCES = 8;

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
     * Pending deltas by ring slot: a {@link PointsToSet}, packed words or a
     * {@link SparseBitSet.PackedSnapshot}.
     */
    private @Nullable Object[] ringDeltas = new Object[INITIAL_CAPACITY];

    /**
     * By ring slot: whether the slot's delta is a set that other slots
     * may hold too, so that a merge copies it first.
     */
    private boolean[] ringShared = new boolean[INITIAL_CAPACITY];

    /**
     * The sets received by the current fan-out, in {@code [0, fanSize)}; a
     * forgotten source is null.
     */
    private final @Nullable PointsToSet[] fanSources = new PointsToSet[FAN_OUT_SOURCES];

    /**
     * The stored delta of each fan-out source: a set or packed words.
     */
    private final @Nullable Object[] fanStored = new Object[FAN_OUT_SOURCES];

    /**
     * The insertion number of the first entry holding each stored delta.
     */
    private final int[] fanFirstSeq = new int[FAN_OUT_SOURCES];

    /**
     * Whether each stored set is already flagged shared in every slot
     * holding it.
     */
    private final boolean[] fanFlagged = new boolean[FAN_OUT_SOURCES];

    private int fanSize;

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
     * The packs that took a snapshot of a set's packed words by reference.
     */
    private long packedByReference;

    /**
     * Words of the packs that copied a set's words, and of those that took
     * them by reference.
     */
    private long packedCopyWords;

    private long packedReferenceWords;

    private long sharedEntries;

    private long sharedCopies;

    /**
     * Whether the measurement counters below are kept; they change no
     * result and no order.
     */
    private final boolean counting;

    /**
     * Objects in the polled deltas and in the differences their
     * propagations made, and the polls whose difference was empty
     * (see {@link #recordPropagation}).
     */
    private long polledBits;

    private long diffBits;

    private long emptyDiffPolls;

    /**
     * Estimated bytes of the packed words of the deltas made by packing
     * a large set.
     */
    private long packedBytes;

    /**
     * Merges into a pending delta that already held every object added.
     */
    private long mergesUnchanged;

    /**
     * @param ptsFactory the factory of the pending sets
     * @param packLarge  whether a pending delta that is a large set on
     *                   arrival is held as packed words
     */
    WorkList(PointsToSetFactory ptsFactory, boolean packLarge) {
        this(ptsFactory, packLarge, false);
    }

    /**
     * @param ptsFactory the factory of the pending sets
     * @param packLarge  whether a pending delta that is a large set on
     *                   arrival is held as packed words
     * @param counting   whether the measurement counters are kept
     */
    WorkList(PointsToSetFactory ptsFactory, boolean packLarge, boolean counting) {
        this.ptsFactory = ptsFactory;
        this.packLarge = packLarge;
        this.counting = counting;
    }

    /**
     * Adds the set to the pending delta of the pointer, or adds the
     * pointer with a copy of the set.
     */
    void addEntry(Pointer pointer, PointsToSet pointsToSet) {
        int slot = pendingSlot(pointer);
        if (slot >= 0) {
            merge(slot, pointsToSet);
        } else {
            insert(pointer, newDelta(pointsToSet));
        }
    }

    /**
     * {@link #addEntry} for one target of the current fan-out: a new entry
     * reuses the stored delta of an earlier new entry of this fan-out that
     * received the same set. The caller does not change the set before
     * {@link #endFanOut()}.
     */
    void addFanOutEntry(Pointer pointer, PointsToSet pointsToSet) {
        int slot = pendingSlot(pointer);
        if (slot >= 0) {
            merge(slot, pointsToSet);
            return;
        }
        for (int i = 0; i < fanSize; ++i) {
            if (fanSources[i] == pointsToSet) {
                insertShared(pointer, i);
                return;
            }
        }
        Object stored = newDelta(pointsToSet);
        int seq = insert(pointer, stored);
        if (fanSize < FAN_OUT_SOURCES) {
            fanSources[fanSize] = pointsToSet;
            fanStored[fanSize] = stored;
            fanFirstSeq[fanSize] = seq;
            fanFlagged[fanSize] = false;
            ++fanSize;
        }
    }

    /**
     * Ends the current fan-out: later entries store their own deltas.
     */
    void endFanOut() {
        Arrays.fill(fanSources, 0, fanSize, null);
        Arrays.fill(fanStored, 0, fanSize, null);
        fanSize = 0;
    }

    /**
     * @return the ring slot of the pointer if it is pending, else -1
     */
    private int pendingSlot(Pointer pointer) {
        int index = pointer.getIndex();
        if (index < seqByIndex.length) {
            int slot = seqByIndex[index] & (ringPointers.length - 1);
            if (ringPointers[slot] == pointer) {
                return slot;
            }
        }
        return -1;
    }

    /**
     * Adds a pointer that is not pending, with its delta.
     *
     * @return the insertion number of the new entry
     */
    private int insert(Pointer pointer, Object delta) {
        if (size == ringPointers.length) {
            growRing();
        }
        int index = pointer.getIndex();
        if (index >= seqByIndex.length) {
            growIndex(index);
        }
        int seq = headSeq + size;
        int slot = seq & (ringPointers.length - 1);
        ringPointers[slot] = pointer;
        ringDeltas[slot] = delta;
        ringShared[slot] = false;
        seqByIndex[index] = seq;
        ++size;
        ++newEntries;
        if (size > pendingPeak) {
            pendingPeak = size;
        }
        return seq;
    }

    /**
     * Adds a pointer that is not pending with the stored delta of fan-out
     * source {@code i}. A stored set is flagged in its first slot when it
     * gets a second holder: no merge has changed it there, as an in-place
     * merge forgets the source.
     */
    private void insertShared(Pointer pointer, int i) {
        Object stored = fanStored[i];
        boolean isSet = stored instanceof PointsToSet;
        if (isSet && !fanFlagged[i]) {
            ringShared[fanFirstSeq[i] & (ringPointers.length - 1)] = true;
            fanFlagged[i] = true;
        }
        int seq = insert(pointer, stored);
        if (isSet) {
            ringShared[seq & (ringPointers.length - 1)] = true;
        }
        ++sharedEntries;
    }

    private void merge(int slot, PointsToSet pointsToSet) {
        Object pending = ringDeltas[slot];
        PointsToSet set;
        if (pending instanceof PointsToSet held) {
            if (ringShared[slot]) {
                set = held.copy();
                ringDeltas[slot] = set;
                ringShared[slot] = false;
                ++sharedCopies;
            } else {
                if (fanSize != 0) {
                    forgetFanOutSource(held);
                }
                set = held;
            }
        } else {
            set = restore(pending);
            ringDeltas[slot] = set;
        }
        boolean changed = set.addAll(pointsToSet);
        ++mergedEntries;
        if (counting && !changed) {
            ++mergesUnchanged;
        }
    }

    /**
     * Stops reusing the stored set that a merge is about to change in
     * place.
     */
    private void forgetFanOutSource(PointsToSet held) {
        for (int i = 0; i < fanSize; ++i) {
            if (fanStored[i] == held) {
                fanSources[i] = null;
                fanStored[i] = null;
            }
        }
    }

    private Object newDelta(PointsToSet pointsToSet) {
        if (packLarge) {
            SparseBitSet.PackedSnapshot snapshot = ptsFactory.packedLargeSnapshot(pointsToSet);
            if (snapshot != null) {
                ++packs;
                ++packedByReference;
                packedReferenceWords += snapshot.length();
                return snapshot;
            }
            long[] packed = ptsFactory.toPackedLarge(pointsToSet);
            if (packed != null) {
                ++packs;
                packedCopyWords += packed.length;
                if (counting) {
                    packedBytes += longArrayBytes(packed);
                }
                return packed;
            }
        }
        return pointsToSet.copy();
    }

    /**
     * @return a new set restored from a packed pending delta: packed words
     * or a snapshot of them.
     */
    private PointsToSet restore(Object packed) {
        ++unpacks;
        return packed instanceof SparseBitSet.PackedSnapshot snapshot
                ? ptsFactory.ofPackedLarge(snapshot)
                : ptsFactory.ofPackedLarge((long[]) packed);
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
        boolean[] newShared = new boolean[oldCapacity * 2];
        for (int i = 0; i < size; ++i) {
            int seq = headSeq + i;
            newPointers[seq & newMask] = ringPointers[seq & oldMask];
            newDeltas[seq & newMask] = ringDeltas[seq & oldMask];
            newShared[seq & newMask] = ringShared[seq & oldMask];
        }
        ringPointers = newPointers;
        ringDeltas = newDeltas;
        ringShared = newShared;
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
        ringShared[slot] = false;
        ++headSeq;
        --size;
        if (fanSize != 0) {
            endFanOut();
        }
        if (pending instanceof PointsToSet set) {
            polledDelta = set;
        } else {
            polledDelta = restore(pending);
        }
        return pointer;
    }

    /**
     * @return the delta of the pointer returned by the last
     * {@link #pollPointer()}; it can be taken once. The caller only reads
     * it: other pending pointers may hold the same set.
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
     * @return the packs that took a set's packed words by reference
     */
    long packedByReference() {
        return packedByReference;
    }

    /**
     * @return the bytes of the words that packs copied
     */
    long packedCopyBytes() {
        return packedCopyWords * Long.BYTES;
    }

    /**
     * @return the bytes of the words that packs took by reference
     */
    long packedReferenceBytes() {
        return packedReferenceWords * Long.BYTES;
    }

    /**
     * @return the new entries that reused a stored delta of their fan-out
     */
    long sharedEntries() {
        return sharedEntries;
    }

    /**
     * @return the merges that first copied a shared set
     */
    long sharedCopies() {
        return sharedCopies;
    }

    /**
     * @return the counters of the pointer entries, for the log.
     */
    String countersLine() {
        String line = "pending_pointers=" + size
                + " pending_peak=" + pendingPeak
                + " new_entries=" + newEntries
                + " merged_entries=" + mergedEntries
                + " packs=" + packs
                + " unpacks=" + unpacks
                + " shared_entries=" + sharedEntries
                + " shared_copies=" + sharedCopies
                + " packed_by_reference=" + packedByReference
                + " packed_copy_bytes=" + packedCopyBytes()
                + " packed_reference_bytes=" + packedReferenceBytes();
        if (!counting) {
            return line;
        }
        long[] pending = pendingFootprint();
        return line
                + " polled_bits=" + polledBits
                + " diff_bits=" + diffBits
                + " empty_diff_polls=" + emptyDiffPolls
                + " packed_bytes=" + packedBytes
                + " merges_unchanged=" + mergesUnchanged
                + " pending_packed_bytes=" + pending[0]
                + " pending_set_objects=" + pending[1]
                + " pending_reference_bytes=" + pending[2];
    }

    /**
     * @return whether the measurement counters are kept.
     */
    boolean isCounting() {
        return counting;
    }

    /**
     * Counts one propagation of a polled delta when the counters are kept.
     *
     * @param polledSize the objects in the polled delta
     * @param diffSize   the objects in the difference its propagation made
     */
    void recordPropagation(int polledSize, int diffSize) {
        if (counting) {
            polledBits += polledSize;
            diffBits += diffSize;
            if (diffSize == 0) {
                ++emptyDiffPolls;
            }
        }
    }

    long polledBits() {
        return polledBits;
    }

    long diffBits() {
        return diffBits;
    }

    long emptyDiffPolls() {
        return emptyDiffPolls;
    }

    long packedBytes() {
        return packedBytes;
    }

    long mergesUnchanged() {
        return mergesUnchanged;
    }

    /**
     * Walks the pending entries; an entry that shares its delta counts it
     * again.
     *
     * @return the estimated bytes of the pending packed deltas, the
     * objects in the pending deltas held as sets, and the estimated bytes
     * of the packed words that pending snapshots reference (shared with the
     * set they were taken from while that set is unchanged).
     */
    long[] pendingFootprint() {
        long packedPending = 0;
        long setObjects = 0;
        long referencedPending = 0;
        int mask = ringPointers.length - 1;
        for (int i = 0; i < size; ++i) {
            Object pending = ringDeltas[(headSeq + i) & mask];
            if (pending instanceof long[] packed) {
                packedPending += longArrayBytes(packed);
            } else if (pending instanceof PointsToSet set) {
                setObjects += set.size();
            } else if (pending instanceof SparseBitSet.PackedSnapshot snapshot) {
                referencedPending += 16L + 8L * snapshot.length();
            }
        }
        return new long[]{packedPending, setObjects, referencedPending};
    }

    /**
     * @return the estimated bytes of a {@code long[]} on a 64-bit JVM
     * with compressed oops: a 16-byte header and eight bytes a word.
     */
    private static long longArrayBytes(long[] words) {
        return 16L + 8L * words.length;
    }
}
