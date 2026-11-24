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

import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.collection.Maps;

import java.util.ArrayDeque;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * Represents work list in pointer analysis.
 */
final class WorkList {

    /**
     * Pointer entries to be processed. A pending delta is held either as
     * a {@link PointsToSet} or, when it was a large set on arrival, as the
     * packed words of {@link PointsToSetFactory#toPackedLarge}: a large
     * delta usually holds few bits per bit set block, and many deltas wait
     * at the same time. A packed delta that receives more objects is
     * restored to a set, so merging works on sets as before.
     */
    private final Map<Pointer, Object> pointerEntries = Maps.newLinkedHashMap();

    /**
     * Call edges to be processed.
     */
    private final Queue<Edge<CSCallSite, CSMethod>> callEdges = new ArrayDeque<>();

    private final PointsToSetFactory ptsFactory;

    WorkList(PointsToSetFactory ptsFactory) {
        this.ptsFactory = ptsFactory;
    }

    void addEntry(Pointer pointer, PointsToSet pointsToSet) {
        Object pending = pointerEntries.get(pointer);
        if (pending instanceof PointsToSet set) {
            set.addAll(pointsToSet);
        } else if (pending instanceof long[] packed) {
            PointsToSet set = ptsFactory.ofPackedLarge(packed);
            set.addAll(pointsToSet);
            pointerEntries.put(pointer, set);
        } else {
            long[] packed = ptsFactory.toPackedLarge(pointsToSet);
            pointerEntries.put(pointer, packed != null ? packed : pointsToSet.copy());
        }
    }

    void addEntry(Edge<CSCallSite, CSMethod> edge) {
        callEdges.add(edge);
    }

    Entry pollEntry() {
        if (!callEdges.isEmpty()) {
            // for correctness, we need to ensure that any call edges in
            // the work list must be processed prior to the pointer entries
            return new CallEdgeEntry(callEdges.poll());
        } else if (!pointerEntries.isEmpty()) {
            var it = pointerEntries.entrySet().iterator();
            var e = it.next();
            it.remove();
            PointsToSet set = e.getValue() instanceof long[] packed
                    ? ptsFactory.ofPackedLarge(packed)
                    : (PointsToSet) e.getValue();
            return new PointerEntry(e.getKey(), set);
        } else {
            throw new NoSuchElementException();
        }
    }

    boolean isEmpty() {
        return pointerEntries.isEmpty() && callEdges.isEmpty();
    }

    /**
     * @return the number of pending pointer entries.
     */
    int pointerEntryCount() {
        return pointerEntries.size();
    }

    /**
     * @return the number of pending call edges.
     */
    int callEdgeCount() {
        return callEdges.size();
    }

    interface Entry {
    }

    record PointerEntry(Pointer pointer, PointsToSet pointsToSet)
            implements Entry {
    }

    record CallEdgeEntry(Edge<CSCallSite, CSMethod> edge)
            implements Entry {
    }
}
