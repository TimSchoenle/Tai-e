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
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.EdgeSourceCensus;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.pts.PointsToSetCensus;

import java.util.stream.Stream;

/**
 * The census taken at the solver's finish with the option {@code census}
 * (before any release), for sizing PFG cycle collapse and a packed
 * points-to set form:
 * <ul>
 *     <li>the SCCs of the pointer flow graph restricted to the edges that
 *     pass every object unchanged: an edge of the class
 *     {@link PointerFlowEdge} itself (or stored without an edge object),
 *     of a kind other than {@link FlowKind#OTHER} (plugin edges), with the
 *     transfer {@link Identity}, into a pointer without filters;</li>
 *     <li>the block census of the points-to sets of all pointers;</li>
 *     <li>the census of the context-sensitive objects ({@link CSObjCensus});</li>
 *     <li>the census of the sources of the sourced call edges
 *     ({@link EdgeSourceCensus}) over the reachable CS methods, logged with
 *     its own wall time.</li>
 * </ul>
 * Mock pointers are included in the first two. The graph's edges are the
 * qualifying edge transfers (one per edge and transfer).
 */
record SolverCensus(PfgSccCensus scc, PointsToSetCensus pts, CSObjCensus objs,
                    EdgeSourceCensus edgeSources) {

    private static final Logger logger = LoggerFactory.getLogger(SolverCensus.class);

    /**
     * Takes the census of the pointers of the manager and logs it.
     */
    static SolverCensus take(CSManager csManager, CSCallGraph callGraph) {
        Pointer[] byIndex = pointersByIndex(csManager);
        int n = byIndex.length;
        int[] start = new int[n + 1];
        for (int u = 0; u < n; u++) {
            start[u + 1] = start[u] + countUnfiltered(byIndex[u]);
        }
        int[] targets = new int[start[n]];
        int[] fill = new int[1];
        for (Pointer p : byIndex) {
            if (p != null) {
                fill[0] = start[p.getIndex()];
                p.forEachOutTransfer((edge, target, transfer) -> {
                    if (isUnfiltered(edge, target, transfer)) {
                        targets[fill[0]++] = target.getIndex();
                    }
                });
            }
        }
        PfgSccCensus scc = PfgSccCensus.of(start, targets);
        PointsToSetCensus pts = new PointsToSetCensus();
        for (Pointer p : byIndex) {
            if (p != null) {
                pts.add(p.getPointsToSet());
            }
        }
        pts.finish();
        CSObjCensus objs = CSObjCensus.take(csManager);
        long edgeStart = System.nanoTime();
        EdgeSourceCensus edgeSources = new EdgeSourceCensus();
        callGraph.reachableMethods().forEach(edgeSources::add);
        long edgeMillis = (System.nanoTime() - edgeStart) / 1_000_000;
        SolverCensus census = new SolverCensus(scc, pts, objs, edgeSources);
        logger.info("{}\n{}\n{}\n{} wall_ms={}", scc, pts, objs, edgeSources, edgeMillis);
        return census;
    }

    private static Pointer[] pointersByIndex(CSManager csManager) {
        int max = allPointers(csManager).mapToInt(Pointer::getIndex).max().orElse(-1);
        Pointer[] byIndex = new Pointer[max + 1];
        allPointers(csManager).forEach(p -> byIndex[p.getIndex()] = p);
        return byIndex;
    }

    private static Stream<Pointer> allPointers(CSManager csManager) {
        return Stream.concat(csManager.pointers(), csManager.mockPointers());
    }

    private static int countUnfiltered(@Nullable Pointer p) {
        if (p == null) {
            return 0;
        }
        int[] count = new int[1];
        p.forEachOutTransfer((edge, target, transfer) -> {
            if (isUnfiltered(edge, target, transfer)) {
                count[0]++;
            }
        });
        return count[0];
    }

    /**
     * @return true if the transfer on the edge passes every object of the
     * source to the target unchanged; see the class comment.
     */
    static boolean isUnfiltered(@Nullable PointerFlowEdge edge, Pointer target,
                                Transfer transfer) {
        return transfer == Identity.INSTANCE
                && (edge == null || (edge.getClass() == PointerFlowEdge.class
                && edge.kind() != FlowKind.OTHER))
                && target.getFilters().isEmpty();
    }
}
