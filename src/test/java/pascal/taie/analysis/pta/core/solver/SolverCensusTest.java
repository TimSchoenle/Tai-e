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

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetCensus;

import java.lang.reflect.Field;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code census}: off by default; on, the solver takes the census
 * before the plugins' onFinish, over every pointer (mock pointers
 * included).
 */
public class SolverCensusTest {

    @Test
    void offByDefault() {
        run("");
        assertNull(Probe.census);
    }

    @Test
    void countsEveryPointerAndTheLoopCycle() {
        run("census:true;");
        SolverCensus census = Probe.census;
        assertNotNull(census, "no census at onFinish");
        PointsToSetCensus pts = census.pts();
        assertEquals(Probe.pointers, pts.all().sets());
        assertEquals(Probe.objects, pts.all().objects());
        // without sharing every non-null set is its own object
        assertEquals(Probe.nonNullSets, pts.distinct().sets());
        assertEquals(Probe.distinctSets, pts.distinct().sets());
        assertEquals(Probe.unfilteredEdges, census.scc().edges());
        assertTrue(pts.bytesToday() > 0);
        assertTrue(pts.bytesPacked() > 0);
    }

    /**
     * Without the library, the swap loop {@code t = x; x = y; y = t} of
     * Census.main is the only cycle of copies: x, t and y form one SCC of
     * three local assignment edges.
     */
    @Test
    void swapLoopIsTheOnlyCycleOfTheApplication() {
        run("census:true;only-app:true;");
        PfgSccCensus scc = Probe.census.scc();
        assertEquals(1, scc.cyclicSccs(), scc.toString());
        assertEquals(3, scc.nodesInside(), scc.toString());
        assertEquals(3, scc.edgesInside(), scc.toString());
        assertEquals(3, scc.largest(), scc.toString());
        assertEquals(1, scc.sizeHistogram()[2], scc.toString());
    }

    @Test
    void distinctSetsAreTheSharedOnes() {
        run("census:true;share-points-to-sets:true;");
        PointsToSetCensus pts = Probe.census.pts();
        assertEquals(Probe.pointers, pts.all().sets());
        assertEquals(Probe.distinctSets, pts.distinct().sets());
        assertTrue(pts.distinct().sets() < Probe.nonNullSets,
                "no set is shared: " + pts);
    }

    private static void run(String options) {
        Probe.census = null;
        Main.main("-cp", "src/test/resources/pta/census",
                "-m", "Census",
                "-a", "pta=" + options + "plugins:[" + Probe.class.getName() + "];");
    }

    /**
     * Reads the census at onFinish and counts, independently of it, the
     * pointers, their objects, their distinct set objects and the
     * unfiltered out edges.
     */
    public static class Probe implements Plugin {

        static SolverCensus census;

        static long pointers;

        static long objects;

        static long distinctSets;

        static long nonNullSets;

        static long unfilteredEdges;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            try {
                Field field = DefaultSolver.class.getDeclaredField("census");
                field.setAccessible(true);
                census = (SolverCensus) field.get(solver);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
            CSManager csManager = solver.getCSManager();
            Set<PointsToSet> distinct = Collections.newSetFromMap(new IdentityHashMap<>());
            long[] counts = new long[4];
            Stream.concat(csManager.pointers(), csManager.mockPointers()).forEach(p -> {
                counts[0]++;
                PointsToSet pts = p.getPointsToSet();
                if (pts != null) {
                    counts[1] += pts.size();
                    counts[3]++;
                    distinct.add(pts);
                }
                p.forEachOutTransfer((edge, target, transfer) -> {
                    if (transfer == Identity.INSTANCE && target.getFilters().isEmpty()
                            && (edge == null || (edge.getClass() == PointerFlowEdge.class
                            && edge.kind() != FlowKind.OTHER))) {
                        counts[2]++;
                    }
                });
            });
            pointers = counts[0];
            objects = counts[1];
            distinctSets = distinct.size();
            unfilteredEdges = counts[2];
            nonNullSets = counts[3];
        }
    }
}
