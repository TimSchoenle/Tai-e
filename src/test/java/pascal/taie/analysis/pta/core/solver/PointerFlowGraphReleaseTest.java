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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Plugin hook {@code onRelease} and option
 * {@code release-pointer-flow-graph}: with {@code release-solver-state},
 * the solver drops the out edges of every pointer and then calls
 * onRelease, right before onFinish; the points-to sets and the call graph
 * of the result are the same as without the release.
 */
public class PointerFlowGraphReleaseTest {

    private static final String RELEASE =
            "release-solver-state:true;release-pointer-flow-graph:true;";

    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "src/test/resources/pta/lambda|ImpreciseLambdas|implicit-entries:false;"
                    + "only-app:true;handle-invokedynamic:true;",
            "src/test/resources/pta/lambda|LambdaContexts|cs:1-obj;implicit-entries:false;"
                    + "only-app:true;handle-invokedynamic:true;",
    })
    void releaseKeepsResultQueriesAndDropsOutEdges(String classPath, String main,
                                                   String options) throws Exception {
        // only-app: the sorted points-to lines of the whole JDK would not
        // fit twice into the test heap
        String base = options + "plugins:[" + ReleaseProbe.class.getName() + "];";
        run(classPath, main, base);
        List<String> pointsTo = pointsTo(result());
        List<String> callGraph = callGraph(result());
        assertEquals(List.of("finish"), ReleaseProbe.events,
                "onRelease ran without release-solver-state");
        assertTrue(ReleaseProbe.outDegreeAtFinish > 0, "no out edge to release");
        assertFalse(pointsTo.isEmpty());
        assertFalse(callGraph.isEmpty());

        run(classPath, main, RELEASE + base);
        assertEquals(List.of("release", "finish"), ReleaseProbe.events);
        assertEquals(0, ReleaseProbe.liveEdgeArraysAtRelease,
                "an out-edge array was still held at onRelease");
        assertEquals(pointsTo, pointsTo(result()));
        assertEquals(callGraph, callGraph(result()));
        assertEquals(0, liveEdgeArrays(ReleaseProbe.csManager));
        Pointer pointer = ReleaseProbe.csManager.pointers().findFirst().orElseThrow();
        assertThrows(IllegalStateException.class, pointer::getOutEdges);
        assertThrows(IllegalStateException.class, pointer::getOutDegree);
        assertThrows(IllegalStateException.class,
                () -> pointer.forEachOutTransfer((edge, target, transfer) -> { }));
        assertThrows(IllegalStateException.class, () -> pointer.removeEdgesIf(e -> false));
        assertThrows(IllegalStateException.class, () -> pointer.addEdge(
                new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, pointer, pointer)));
        assertThrows(IllegalStateException.class, () -> result().getObjectFlowGraph());

        // the option alone, without release-solver-state, releases nothing
        run(classPath, main, "release-pointer-flow-graph:true;" + base);
        assertEquals(List.of("finish"), ReleaseProbe.events);
        assertTrue(ReleaseProbe.outDegreeAtFinish > 0, "the out edges were released");
        assertEquals(pointsTo, pointsTo(result()));
        assertEquals(callGraph, callGraph(result()));
    }

    private static void run(String classPath, String main, String options) {
        Main.main("-cp", classPath, "-m", main, "-a", "pta=" + options);
    }

    private static PointerAnalysisResult result() {
        return World.get().getResult(PointerAnalysis.ID);
    }

    /**
     * @return per pointer of the result (context-sensitive variables,
     * instance fields, array indexes, static fields) and per variable
     * (context-insensitive), its points-to set, sorted.
     */
    private static List<String> pointsTo(PointerAnalysisResult result) {
        List<String> lines = new ArrayList<>();
        Stream.<Collection<? extends Pointer>>of(result.getCSVars(), result.getInstanceFields(),
                        result.getArrayIndexes(), result.getStaticFields())
                .flatMap(Collection::stream)
                .forEach(p -> lines.add(p + " -> " + sorted(p.getObjects())));
        result.getVars().forEach(v -> lines.add(v.getMethod() + "/" + v
                + " -> " + sorted(result.getPointsToSet(v))));
        lines.sort(null);
        return lines;
    }

    private static List<String> callGraph(PointerAnalysisResult result) {
        List<String> lines = new ArrayList<>();
        result.getCSCallGraph().edges().forEach(e -> lines.add(e.toString()));
        result.getCallGraph().edges().forEach(e -> lines.add(e.toString()));
        result.getCallGraph().reachableMethods().forEach(m -> lines.add(m.toString()));
        lines.sort(null);
        return lines;
    }

    private static List<String> sorted(Collection<?> objects) {
        return objects.stream().map(Object::toString).sorted().toList();
    }

    /**
     * @return the number of pointers, mock pointers included, whose
     * out-edge array or out-edge dedup state is still held: not released
     * (the shared empty marker of the edge release has length 0, the dedup
     * release has its own shared marker) and not null.
     */
    private static int liveEdgeArrays(CSManager csManager) throws ReflectiveOperationException {
        Class<?> type = Class.forName(
                "pascal.taie.analysis.pta.core.cs.element.AbstractPointer");
        Field edges = type.getDeclaredField("edges");
        Field dedup = type.getDeclaredField("dedup");
        Field released = type.getDeclaredField("RELEASED");
        edges.setAccessible(true);
        dedup.setAccessible(true);
        released.setAccessible(true);
        Object releasedDedup = released.get(null);
        int live = 0;
        for (Pointer p : Stream.concat(csManager.pointers(), csManager.mockPointers()).toList()) {
            Object[] slots = (Object[]) edges.get(p);
            Object set = dedup.get(p);
            if ((slots != null && slots.length != 0) || (set != null && set != releasedDedup)) {
                ++live;
            }
        }
        return live;
    }

    /**
     * Records the order of onRelease and onFinish, the number of live
     * out-edge arrays at onRelease, and the out degree of all pointers at
     * onFinish when the out edges are kept.
     */
    public static class ReleaseProbe implements Plugin {

        static List<String> events;

        static int liveEdgeArraysAtRelease;

        static long outDegreeAtFinish;

        static CSManager csManager;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            events = new ArrayList<>();
            liveEdgeArraysAtRelease = -1;
            outDegreeAtFinish = -1;
            csManager = solver.getCSManager();
        }

        @Override
        public void onRelease() {
            events.add("release");
            try {
                liveEdgeArraysAtRelease = liveEdgeArrays(csManager);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        @Override
        public void onFinish() {
            events.add("finish");
            if (!events.contains("release")) {
                outDegreeAtFinish = csManager.pointers()
                        .mapToLong(Pointer::getOutDegree).sum();
            }
        }
    }
}
