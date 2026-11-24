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

package pascal.taie.analysis.pta.plugin.exception;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.solver.ProgressCounters;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A wave over at least exception-wave-parallel-threshold call edges skips
 * the callers found, in parallel, to already throw its exceptions, with
 * the same events in the same order as the wave that takes every edge.
 */
public class ExceptionWaveFilterTest {

    private static final String DIR = "exception";

    private static final String FILTER_ALL = "exception-wave-parallel-threshold:1";

    @ParameterizedTest
    @ValueSource(strings = {"ExceptionSharedCallSite", "ExceptionManyCallers",
            "ExceptionTwoHandlers", "ExceptionCircle", "ExceptionCircleAndRecursion",
            "ExceptionTreeAndRecursion", "ExceptionThrownTwice", "ExceptionNoneCaught",
            "ExceptionFromClinit", "ExceptionOverOtherEdges", "CatchDispatch"})
    void filteredWavesGiveTheSameEventsInTheSameOrder(String main) {
        // merged objects use dense sets, unmerged ones sparse sets
        for (String merge : new String[]{"merge-exception-objects:true",
                "merge-exception-objects:false"}) {
            String label = main + " " + merge;
            Run sequential = run(main, merge);
            Run filtered = run(main, merge, FILTER_ALL);
            assertEquals(0, sequential.parallelWaves(), "the default threshold filtered " + label);
            assertEquals(sequential.events(), filtered.events(), label);
            assertEquals(sequential.results(), filtered.results(), label);
            assertEquals(sequential.emptyDiffs(), filtered.emptyDiffs(), label);
            assertEquals(sequential.waveStats(), filtered.waveStats(), label);
            assertEquals(sequential.counters(), filtered.counters(),
                    "visits, edges visited, progress empty diffs, entries drained " + label);
        }
    }

    /**
     * The waves of the second and third callee of the shared call sites
     * find them covered and skip them.
     */
    @Test
    void coveredCallersAreSkipped() {
        Run sequential = run("ExceptionSharedCallSite");
        Run filtered = run("ExceptionSharedCallSite", FILTER_ALL);
        System.out.println("ExceptionSharedCallSite sequential: " + sequential.waveStats()
                + "; filtered: " + filtered.parallelWaves() + " parallel waves, "
                + filtered.skippedEdges() + " edges skipped");
        assertEquals(0, sequential.skippedEdges());
        assertTrue(filtered.parallelWaves() > 0, "no wave was filtered");
        assertTrue(filtered.skippedEdges() > 0, "no covered caller was skipped");
    }

    /**
     * Repeated filtered runs (parallel on every wave) agree with each other.
     */
    @Test
    void repeatedFilteredRunsAgree() {
        Run first = run("ExceptionSharedCallSite", FILTER_ALL);
        for (int i = 0; i < 5; i++) {
            Run again = run("ExceptionSharedCallSite", FILTER_ALL);
            assertEquals(first.events(), again.events());
            assertEquals(first.results(), again.results());
            assertEquals(first.skippedEdges(), again.skippedEdges());
        }
    }

    private static Run run(String main, String... opts) {
        String[] all = new String[opts.length + 1];
        all[0] = "plugins:[" + Recorder.class.getName() + "]";
        System.arraycopy(opts, 0, all, 1, opts.length);
        Recorder.last = null;
        Tests.testPTA(false, DIR, main, all);
        assertTrue(Recorder.last != null, "no run recorded for " + main);
        return Recorder.last;
    }

    /**
     * @param events      in order: every object the exception analysis
     *                    adds to a variable, and every points-to set the
     *                    solver hands to the plugins
     * @param results     the throw results of every CS method
     */
    private record Run(List<String> events, List<String> results, long emptyDiffs,
                       String waveStats, long parallelWaves, long skippedEdges,
                       List<Long> counters) {
    }

    /**
     * Records the events and, after the solve, the results and counters.
     */
    public static class Recorder implements Plugin {

        static Run last;

        private Solver solver;

        private List<String> events;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            List<String> recorded = new ArrayList<>();
            events = recorded;
            Solver real = solver;
            Solver recording = (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> {
                        if (method.getName().equals("addVarPointsTo")
                                && args.length == 3 && args[2] instanceof CSObj obj) {
                            Var var = (Var) args[1];
                            recorded.add("add " + args[0] + ":" + var + "@"
                                    + var.getMethod() + " <- " + obj);
                        }
                        try {
                            return method.invoke(real, args);
                        } catch (InvocationTargetException e) {
                            throw e.getCause();
                        }
                    });
            ExceptionAnalysisAccess.replaceSolver(solver, recording);
        }

        @Override
        public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
            events.add("pts " + csVar + " <- " + pts);
        }

        @Override
        public void onFinish() {
            ExceptionAnalysis analysis = ExceptionAnalysisAccess.of(solver);
            List<String> results = new ArrayList<>();
            for (CSMethod csMethod : solver.getCallGraph()) {
                CSMethodThrowResult result = csMethod.getThrowResult();
                if (result == null) {
                    continue;
                }
                results.add(csMethod + " uncaught " + result.mayThrowUncaught());
                for (Stmt stmt : csMethod.getMethod().getIR()) {
                    results.add(csMethod + " " + stmt + " "
                            + result.mayThrowExplicitly(stmt));
                }
            }
            assertFalse(results.isEmpty(), "no throw result recorded");
            // the call graph iterates its methods in no fixed order
            results.sort(null);
            ProgressCounters progress = solver.getProgressCounters();
            List<Long> counters = List.of(analysis.visits, progress.getEdgesVisited(),
                    progress.getEmptyDiffs(), progress.getEntriesDrained());
            last = new Run(List.copyOf(events), results, analysis.emptyDiffs,
                    analysis.waveStats.toString(), analysis.parallelWaves,
                    analysis.skippedEdges, counters);
        }
    }
}
