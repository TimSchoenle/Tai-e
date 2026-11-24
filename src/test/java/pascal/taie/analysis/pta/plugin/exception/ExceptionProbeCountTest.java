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
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.pta.core.solver.ProgressCounters;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The exception state sits on typed fields: a visit probes no map except
 * the explicit-exception map of a throw statement, and a CS method's
 * catcher table is probed once, when its result is created.
 */
class ExceptionProbeCountTest {

    @Test
    void visitsProbeFewerMapsThanOnePerLookup() {
        Tests.testPTA(false, "exception", "ExceptionManyCallers",
                "plugins:[" + ProbeRecorder.class.getName() + "]");
        long visits = ProbeRecorder.visits;
        long newDiffs = visits - ProbeRecorder.emptyDiffs;
        // a lookup per kind and visit: the result of the CS method, the
        // statement's thrown set, and for a new diff the method's catcher
        // map and its statement entry; plus the callee's result per edge
        long onePerLookup = 2 * visits + 2 * newDiffs + ProbeRecorder.callEdgeReads;
        System.out.println("exception map probes: " + ProbeRecorder.mapProbes
                + " (one per lookup: " + onePerLookup + ", visits " + visits
                + ", new diffs " + newDiffs + ")");
        assertTrue(visits > 0, "the program propagates exceptions");
        assertTrue(ProbeRecorder.mapProbes < onePerLookup,
                "typed fields replace most map probes");
        assertEquals(ProbeRecorder.emptyDiffs, ProbeRecorder.progressEmptyDiffs,
                "the progress counters see every empty diff");
        assertTrue(ProbeRecorder.drained >= visits,
                "every visit comes from a drained entry or wave edge");
    }

    public static class ProbeRecorder implements Plugin {

        static long visits = -1;

        static long emptyDiffs = -1;

        static long callEdgeReads = -1;

        static long mapProbes = -1;

        static long progressEmptyDiffs = -1;

        static long drained = -1;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            ExceptionAnalysis analysis = ExceptionAnalysisAccess.of(solver);
            visits = analysis.visits;
            emptyDiffs = analysis.emptyDiffs;
            callEdgeReads = analysis.callEdgeReads;
            mapProbes = analysis.mapProbes;
            ProgressCounters counters = solver.getProgressCounters();
            progressEmptyDiffs = counters.getEmptyDiffs();
            drained = counters.getEntriesDrained();
        }
    }
}
