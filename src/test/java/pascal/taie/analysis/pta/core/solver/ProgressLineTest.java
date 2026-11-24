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

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The solver's progress line when the check fires: the probe checks at
 * every work list entry, so the small test program reaches the line. The
 * line must not change the work the solver does, and the plugin-side
 * counters start from zero in every solve.
 */
class ProgressLineTest {

    @AfterEach
    void restoreHook() {
        ProgressProbePlugin.hookIntervalNanos = ProgressProbePlugin.NO_HOOK;
    }

    private static void solve(String progressInterval, long hookIntervalNanos) {
        ProgressProbePlugin.clear();
        ProgressProbePlugin.hookIntervalNanos = hookIntervalNanos;
        Main.main("-cp", "src/test/resources/pta",
                "-cp", "src/test/resources/pta/basic",
                "-m", "Assign",
                "-a", "pta=cs:1-call;only-app:true;implicit-entries:false;"
                        + "progress-interval:" + progressInterval + ";"
                        + "plugins:[pascal.taie.analysis.pta.core.solver.ProgressProbePlugin];");
    }

    @Test
    void firedProgressLinesDoNotChangeTheSolve() {
        solve("0", ProgressProbePlugin.NO_HOOK);
        long iterations = ProgressProbePlugin.iterations;
        long csCallEdges = ProgressProbePlugin.csCallEdges;
        long graphEdges = ProgressProbePlugin.graphEdges;
        List<String> callEdges = ProgressProbePlugin.callEdges;
        List<String> pointsTo = ProgressProbePlugin.pointsTo;
        assertEquals(0, ProgressProbePlugin.progressLines);
        assertFalse(pointsTo.isEmpty(), "the program has points-to facts");
        assertTrue(graphEdges > 0, "the program has call edges");

        solve("60", 1);
        assertTrue(ProgressProbePlugin.progressLines > 0,
                "a 1 ns interval checked at every entry logs lines");
        assertTrue(ProgressProbePlugin.progressLines <= ProgressProbePlugin.iterations,
                "at most one line per work list entry");
        assertEquals(iterations, ProgressProbePlugin.iterations,
                "the progress line does not change the work the solver does");
        assertEquals(csCallEdges, ProgressProbePlugin.csCallEdges);
        assertEquals(graphEdges, ProgressProbePlugin.graphEdges);
        assertEquals(graphEdges, ProgressProbePlugin.csCallEdges);
        assertEquals(callEdges, ProgressProbePlugin.callEdges, "same call graph");
        assertEquals(pointsTo, ProgressProbePlugin.pointsTo, "same points-to sets");
    }

    @Test
    void intervalZeroLogsNothingWhenCheckedAtEveryEntry() {
        solve("60", 0);
        assertTrue(ProgressProbePlugin.iterations > 0);
        assertEquals(0, ProgressProbePlugin.progressLines);
    }

    @Test
    void pluginCountersStartFromZeroInEverySolve() {
        solve("0", ProgressProbePlugin.NO_HOOK);
        assertEquals(0, ProgressProbePlugin.countersAtStart,
                "counters bumped before the solve are cleared when it starts");
    }
}
