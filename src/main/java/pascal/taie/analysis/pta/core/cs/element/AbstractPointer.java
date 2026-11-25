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

package pascal.taie.analysis.pta.core.cs.element;

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.solver.Identity;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Transfer;
import pascal.taie.analysis.pta.core.solver.TypeFilter;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.util.collection.ArraySet;
import pascal.taie.util.collection.IntArraySets;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;

abstract class AbstractPointer implements Pointer {

    private PointsToSet pointsToSet;

    private final int index;

    /**
     * The out-edge dedup state; it only dedupes
     * {@link #addEdge(PointerFlowEdge)} and
     * {@link #addEdge(PointerFlowEdge, Transfer)} by target: null or an
     * {@link OutEdgeIndex} table of {@link #edges} (null while {@link #edges}
     * has at most {@link OutEdgeIndex#LINEAR_ENTRIES} entries), until
     * {@link #removeEdgesIf} first removes an edge; from then on an
     * {@link EverAdded}, as a removed target still counts as present;
     * {@link #RELEASED} after {@link #releaseEdgeDedup()}.
     */
    private @Nullable Object dedup;

    /**
     * Marks {@link #dedup} as released by {@link #releaseEdgeDedup()}.
     */
    private static final Object RELEASED = new Object();

    /**
     * Indexes of the targets of every out edge ever added, an
     * {@link IntArraySets} set: the dedup state after a removal.
     */
    private static final class EverAdded {
        private int[] targets;

        private EverAdded(int[] targets) {
            this.targets = targets;
        }
    }

    /**
     * Slots per out edge in {@link #edges}.
     */
    static final int SLOTS = 2;

    /**
     * Out edges in insertion order, {@link #SLOTS} slots each, or null
     * before the first edge. An edge stored as an object has the
     * {@link PointerFlowEdge} in its first slot and null in the second. An
     * edge stored without an object (see {@link #addEdge(PointerFlowEdge,
     * Transfer)}) has its target in the first slot and a tag for its
     * {@link FlowKind} and its only transfer in the second: the kind itself
     * for {@link Identity}, {@link TypeFilter#edgeTag(FlowKind)} for a
     * {@link TypeFilter}. The edges fill a
     * prefix of the array; the first slot of each unused entry is null.
     * (No count field: it would enlarge every pointer object.)
     */
    private Object @Nullable [] edges;

    /**
     * Marks {@link #edges} as released by {@link #releaseOutEdges()}; its
     * length 0 is never that of a live array.
     */
    private static final Object[] RELEASED_EDGES = new Object[0];

    private Set<Predicate<CSObj>> filters = Set.of();

    protected AbstractPointer(int index) {
        this.index = index;
    }

    @Override
    public int getIndex() {
        return index;
    }

    @Override
    public PointsToSet getPointsToSet() {
        return pointsToSet;
    }

    @Override
    public void setPointsToSet(PointsToSet pointsToSet) {
        this.pointsToSet = pointsToSet;
    }

    @Override
    public void addFilter(Predicate<CSObj> filter) {
        if (filters.isEmpty()) {
            filters = Sets.newHybridSet();
        }
        filters.add(filter);
    }

    @Override
    public Set<Predicate<CSObj>> getFilters() {
        return filters;
    }

    @Override
    public Set<CSObj> getObjects() {
        PointsToSet pts = getPointsToSet();
        return pts == null ? Set.of() : pts.getObjects();
    }

    @Override
    public Stream<CSObj> objects() {
        return getObjects().stream();
    }

    @Override
    public PointerFlowEdge addEdge(PointerFlowEdge edge) {
        assert edge.source() == this;
        if (addTarget(edge.target().getIndex())) {
            append(edge, null, true);
            return edge;
        } else if (edge.kind() == FlowKind.OTHER) {
            Object[] slots = edges;
            int end = used();
            for (int i = 0; i < end; i += SLOTS) {
                if (slots[i] instanceof PointerFlowEdge outEdge) {
                    if (outEdge.equals(edge)) {
                        return outEdge;
                    }
                } else if (edge.getClass() == PointerFlowEdge.class
                        && slots[i].equals(edge.target())) {
                    // equal to an edge stored without an object: the
                    // caller may add transfers to the returned edge, so it
                    // is stored as an object from now on
                    PointerFlowEdge outEdge = materialize(slots, i);
                    slots[i] = outEdge;
                    slots[i + 1] = null;
                    return outEdge;
                }
            }
            append(edge, null, false);
            return edge;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     * <p>
     * An edge of the class {@link PointerFlowEdge} itself, of a kind other
     * than {@link FlowKind#OTHER}, without transfers and with the transfer
     * {@link Identity} or a {@link TypeFilter} (neither reads the edge) is
     * stored as its target and one tag for its transfer and kind, without
     * the edge object:
     * {@link #getOutEdges()} returns a new edge object for it each time.
     */
    @Override
    public @Nullable PointerFlowEdge addEdge(PointerFlowEdge edge, Transfer transfer) {
        if (edge.getClass() != PointerFlowEdge.class
                || edge.kind() == FlowKind.OTHER
                || edge.hasTransfers()
                || !(transfer == Identity.INSTANCE || transfer.getClass() == TypeFilter.class)) {
            return Pointer.super.addEdge(edge, transfer);
        }
        assert edge.source() == this;
        if (!addTarget(edge.target().getIndex())) {
            return null;
        }
        FlowKind kind = edge.kind();
        append(edge.target(), transfer == Identity.INSTANCE
                ? kind : ((TypeFilter) transfer).edgeTag(kind), true);
        edge.addTransfer(transfer);
        return edge;
    }

    /**
     * Records the target of an out edge being added, unless an out edge
     * with that target was added before (and possibly removed).
     *
     * @return whether the target is new; if so the caller appends an
     * entry for it with {@code newTarget} set.
     * @throws IllegalStateException if {@link #releaseEdgeDedup()} released
     *                               the dedup state
     * @throws IllegalArgumentException if the index is negative or
     *                                  {@link Integer#MAX_VALUE}, which
     *                                  {@link IntArraySets} cannot hold
     */
    private boolean addTarget(int target) {
        if (target < 0 || target == Integer.MAX_VALUE) {
            throw new IllegalArgumentException("target index out of range: " + target);
        }
        Object set = dedup;
        if (set == RELEASED) {
            throw new IllegalStateException("the out-edge dedup state of "
                    + this + " was released after the fixed point");
        } else if (set instanceof EverAdded everAdded) {
            int[] added = IntArraySets.add(everAdded.targets, target);
            if (added == null) {
                return false;
            }
            everAdded.targets = added;
            return true;
        }
        return !OutEdgeIndex.contains(set, liveEdges(), target);
    }

    /**
     * Drops {@link #dedup}; the out edges in {@link #edges} stay.
     */
    @Override
    public void releaseEdgeDedup() {
        dedup = RELEASED;
    }

    /**
     * Drops {@link #edges} and {@link #dedup}; later reads and adds of
     * out edges throw.
     */
    @Override
    public void releaseOutEdges() {
        dedup = RELEASED;
        edges = RELEASED_EDGES;
    }

    /**
     * @return {@link #edges}
     * @throws IllegalStateException if {@link #releaseOutEdges()} released it
     */
    private Object @Nullable [] liveEdges() {
        Object[] slots = edges;
        if (slots == RELEASED_EDGES) {
            throw new IllegalStateException("the out edges of " + this
                    + " were released after the fixed point");
        }
        return slots;
    }

    /**
     * @return the number of slots of {@link #edges} in use, found by a
     * binary search for the first unused entry.
     * @throws IllegalStateException if {@link #releaseOutEdges()} released
     *                               {@link #edges}
     */
    private int used() {
        Object[] slots = liveEdges();
        if (slots == null) {
            return 0;
        }
        int low = 0; // entries below low are in use
        int high = slots.length / SLOTS; // entries from high on are unused
        while (low < high) {
            int mid = (low + high) >>> 1;
            if (slots[mid * SLOTS] != null) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        return low * SLOTS;
    }

    /**
     * Appends an entry to {@link #edges} and keeps an {@link OutEdgeIndex}
     * table in {@link #dedup} up to date.
     *
     * @param newTarget whether no other entry has the target of this one
     */
    private void append(Object first, @Nullable Object tag, boolean newTarget) {
        Object[] slots = edges;
        int used = used();
        boolean replaced = true;
        if (slots == null) {
            slots = new Object[SLOTS];
            edges = slots;
        } else if (used == slots.length) {
            int count = used / SLOTS;
            slots = Arrays.copyOf(slots, (count + Math.max(1, count >> 1)) * SLOTS);
            edges = slots;
        } else {
            replaced = false;
        }
        slots[used] = first;
        slots[used + 1] = tag;
        Object set = dedup;
        if (set instanceof EverAdded) {
            return;
        }
        if (replaced) {
            dedup = OutEdgeIndex.build(slots, used / SLOTS + 1);
        } else if (newTarget && set != null) {
            OutEdgeIndex.insert(set, slots, used / SLOTS);
        }
    }

    /**
     * @return the only transfer of an edge stored without an object, from
     * its tag.
     */
    private static Transfer transferOf(Object tag) {
        return tag instanceof FlowKind ? Identity.INSTANCE : ((TypeFilter.EdgeTag) tag).filter();
    }

    /**
     * @return a new edge object for the edge stored without an object at
     * slot {@code i}.
     */
    private PointerFlowEdge materialize(Object[] slots, int i) {
        Object tag = slots[i + 1];
        FlowKind kind = tag instanceof FlowKind identityKind
                ? identityKind : ((TypeFilter.EdgeTag) tag).kind();
        PointerFlowEdge edge = new PointerFlowEdge(kind, this, (Pointer) slots[i]);
        edge.addTransfer(transferOf(tag));
        return edge;
    }

    private PointerFlowEdge edgeAt(Object[] slots, int i) {
        return slots[i] instanceof PointerFlowEdge edge ? edge : materialize(slots, i);
    }

    @Override
    public void forEachOutTransfer(TransferAction action) {
        Object[] slots = liveEdges();
        if (slots == null) {
            return;
        }
        for (int i = 0; i < slots.length; i += SLOTS) {
            Object first = slots[i];
            if (first instanceof PointerFlowEdge edge) {
                Pointer target = edge.target();
                edge.forEachTransfer(transfer -> action.accept(edge, target, transfer));
            } else if (first != null) {
                action.accept(null, (Pointer) first, transferOf(slots[i + 1]));
            } else {
                return;
            }
        }
    }

    @Override
    public void removeEdgesIf(Predicate<PointerFlowEdge> filter) {
        Object[] slots = edges;
        int used = used();
        // test every edge before moving any, so that a filter that throws
        // leaves the edges unchanged
        boolean[] removed = new boolean[used / SLOTS];
        for (int i = 0; i < used; i += SLOTS) {
            removed[i / SLOTS] = filter.test(edgeAt(slots, i));
        }
        int kept = 0;
        boolean any = false;
        for (boolean r : removed) {
            any |= r;
        }
        Object set = dedup;
        if (any && set != RELEASED && !(set instanceof EverAdded)) {
            // the entries in use hold every target ever added, as none
            // was removed before
            int[] targets = null;
            for (int i = 0; i < used; i += SLOTS) {
                int[] added = IntArraySets.add(targets, OutEdgeIndex.targetIndex(slots, i / SLOTS));
                if (added != null) {
                    targets = added;
                }
            }
            dedup = new EverAdded(targets);
        }
        for (int i = 0; i < used; i += SLOTS) {
            if (!removed[i / SLOTS]) {
                if (kept != i) {
                    System.arraycopy(slots, i, slots, kept, SLOTS);
                }
                kept += SLOTS;
            }
        }
        if (kept != used) {
            Arrays.fill(slots, kept, used, null);
        }
    }

    @Override
    public Set<PointerFlowEdge> getOutEdges() {
        Object[] slots = edges;
        int used = used();
        ArrayList<PointerFlowEdge> outEdges = new ArrayList<>(used / SLOTS);
        for (int i = 0; i < used; i += SLOTS) {
            outEdges.add(edgeAt(slots, i));
        }
        return Collections.unmodifiableSet(new ArraySet<>(outEdges, true));
    }

    @Override
    public int getOutDegree() {
        return used() / SLOTS;
    }
}
