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
     * Indexes of the targets of the out-edges, an {@link IntArraySets} set
     * ({@code null} while empty); it only dedupes
     * {@link #addEdge(PointerFlowEdge)} and
     * {@link #addEdge(PointerFlowEdge, Transfer)}.
     */
    private int[] successors;

    /**
     * Marks {@link #successors} as released by {@link #releaseEdgeDedup()};
     * never passed to {@link IntArraySets}.
     */
    private static final int[] RELEASED = new int[0];

    /**
     * Slots per out edge in {@link #edges}.
     */
    private static final int SLOTS = 3;

    /**
     * Out edges in insertion order, {@link #SLOTS} slots each, or null
     * before the first edge. An edge stored as an object has the
     * {@link PointerFlowEdge} in its first slot and null in the others. An
     * edge stored without an object (see {@link #addEdge(PointerFlowEdge,
     * Transfer)}) has its target in the first slot, its only transfer in
     * the second and its {@link FlowKind} in the third. The edges fill a
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
        int[] added = IntArraySets.add(liveSuccessors(), edge.target().getIndex());
        if (added != null) {
            successors = added;
            append(edge, null, null);
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
                    slots[i + 2] = null;
                    return outEdge;
                }
            }
            append(edge, null, null);
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
     * stored as its target, transfer and kind, without the edge object:
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
        int[] added = IntArraySets.add(liveSuccessors(), edge.target().getIndex());
        if (added == null) {
            return null;
        }
        successors = added;
        append(edge.target(), transfer, edge.kind());
        edge.addTransfer(transfer);
        return edge;
    }

    /**
     * @return {@link #successors}
     * @throws IllegalStateException if {@link #releaseEdgeDedup()} released it
     */
    private int[] liveSuccessors() {
        int[] set = successors;
        if (set == RELEASED) {
            throw new IllegalStateException("the out-edge dedup state of "
                    + this + " was released after the fixed point");
        }
        return set;
    }

    /**
     * Drops {@link #successors}; the out edges in {@link #edges} stay.
     */
    @Override
    public void releaseEdgeDedup() {
        successors = RELEASED;
    }

    /**
     * Drops {@link #edges} and {@link #successors}; later reads and adds of
     * out edges throw.
     */
    @Override
    public void releaseOutEdges() {
        successors = RELEASED;
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

    private void append(Object first, @Nullable Transfer transfer, @Nullable FlowKind kind) {
        Object[] slots = edges;
        int used = used();
        if (slots == null) {
            slots = new Object[SLOTS];
            edges = slots;
        } else if (used == slots.length) {
            int count = used / SLOTS;
            slots = Arrays.copyOf(slots, (count + Math.max(1, count >> 1)) * SLOTS);
            edges = slots;
        }
        slots[used] = first;
        slots[used + 1] = transfer;
        slots[used + 2] = kind;
    }

    /**
     * @return a new edge object for the edge stored without an object at
     * slot {@code i}.
     */
    private PointerFlowEdge materialize(Object[] slots, int i) {
        PointerFlowEdge edge = new PointerFlowEdge(
                (FlowKind) slots[i + 2], this, (Pointer) slots[i]);
        edge.addTransfer((Transfer) slots[i + 1]);
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
                action.accept(null, (Pointer) first, (Transfer) slots[i + 1]);
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
