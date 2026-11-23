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
import pascal.taie.World;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.lang.reflect.Field;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Options {@code log-statistics} and {@code release-solver-state}: the
 * first skips the statistics (and the context-insensitive points-to sets
 * they cache), the second releases the solver state that only the solve
 * reads before the plugins' onFinish; the call graph is the same either way.
 */
public class SolverStateOptionsTest {

    @Test
    void statisticsFillTheVarPointsToCacheByDefault() throws Exception {
        run("");
        assertFalse(cachedVarPointsTo().isEmpty());
    }

    @Test
    void skippedStatisticsLeaveTheVarPointsToCacheEmpty() throws Exception {
        run("log-statistics:false;");
        assertTrue(cachedVarPointsTo().isEmpty());
    }

    @Test
    void keepsSolverStateByDefault() {
        run("plugins:[" + Probe.class.getName() + "];");
        Set<String> edges = callEdges();
        assertSame(Probe.workListAtStart, Probe.workListAtFinish);
        assertTrue(Probe.memoCount > 0, "no type filter memo to release");
        assertTrue(Probe.filtersWithMemo > 0, "no type filter holding a memo");
        assertNull(Probe.addEdgeFailure);
        run("release-solver-state:true;plugins:[" + Probe.class.getName() + "];");
        assertEquals(edges, callEdges());
    }

    @Test
    void releasesSolverStateBeforeOnFinish() {
        run("release-solver-state:true;plugins:[" + Probe.class.getName() + "];");
        assertNotNull(Probe.workListAtFinish);
        assertFalse(Probe.workListAtStart == Probe.workListAtFinish,
                "the work list was not replaced");
        assertEquals(0, Probe.memoCount);
        assertEquals(0, Probe.filtersWithMemo);
        assertTrue(Probe.addEdgeFailure instanceof IllegalStateException,
                "a new out edge was accepted after the release: " + Probe.addEdgeFailure);
    }

    private static void run(String options) {
        Main.main("-cp", "src/test/resources/pta/exception",
                "-m", "ExceptionNoneCaught",
                "-a", "pta=" + options);
    }

    private static PointerAnalysisResult result() {
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static Map<?, ?> cachedVarPointsTo() throws Exception {
        return (Map<?, ?>) read(result(), "varPointsTo");
    }

    private static Set<String> callEdges() {
        return result().getCallGraph().edges()
                .map(e -> e.getCallSite().getContainer().getSignature()
                        + " -> " + e.getCallee().getSignature())
                .collect(Collectors.toSet());
    }

    private static Object read(Object owner, String name) throws ReflectiveOperationException {
        Class<?> type = owner instanceof Class<?> c ? c : owner.getClass();
        Field field = type.getDeclaredField(name);
        field.setAccessible(true);
        return field.get(owner instanceof Class<?> ? null : owner);
    }

    /**
     * Records, at onStart and at onFinish, the solver state that
     * {@code release-solver-state} releases, and tries to add a duplicate
     * of an existing out edge at onFinish.
     */
    public static class Probe implements Plugin {

        static Object workListAtStart;

        static Object workListAtFinish;

        static int memoCount;

        static int filtersWithMemo;

        static RuntimeException addEdgeFailure;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            workListAtStart = readSolver("workList");
            workListAtFinish = null;
            memoCount = -1;
            filtersWithMemo = -1;
            addEdgeFailure = null;
        }

        @Override
        public void onFinish() {
            try {
                workListAtFinish = readSolver("workList");
                memoCount = ((Map<?, ?>) read(TypeFilter.class, "memos")).size();
                int holding = 0;
                for (Object filter : ((Map<?, ?>) readSolver("typeFilters")).values()) {
                    if (read(filter, "memo") != null) {
                        ++holding;
                    }
                }
                filtersWithMemo = holding;
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
            // an edge of a kind other than OTHER: without the release, its
            // duplicate is refused and the graph stays unchanged
            PointerFlowEdge existing = solver.getCSManager().pointers()
                    .flatMap(p -> p.getOutEdges().stream())
                    .filter(e -> e.kind() != FlowKind.OTHER)
                    .findFirst()
                    .orElseThrow();
            Pointer source = existing.source();
            try {
                source.addEdge(new PointerFlowEdge(
                        existing.kind(), source, existing.target()));
            } catch (RuntimeException e) {
                addEdgeFailure = e;
            }
        }

        private Object readSolver(String name) {
            try {
                return read(solver, name);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
