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

package pascal.taie.analysis.pta;

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.solver.ProgressCounters;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The solver's progress counters: the context-sensitive call edge counter
 * equals the call graph's edges, a solve with {@code progress-interval:0}
 * logs no progress line, and the plugin-side counters keep what plugins set.
 */
class ProgressCountersTest {

    private static void solve(String progressInterval) {
        ProgressCountersPlugin.iterations = -1;
        ProgressCountersPlugin.csCallEdges = -1;
        ProgressCountersPlugin.graphEdges = -1;
        ProgressCountersPlugin.progressLines = -1;
        ProgressCountersPlugin.phases = -1;
        ProgressCountersPlugin.waves = -1;
        Main.main("-cp", "src/test/resources/pta",
                "-cp", "src/test/resources/pta/basic",
                "-m", "Assign",
                "-a", "pta=cs:1-call;only-app:true;implicit-entries:false;"
                        + "progress-interval:" + progressInterval + ";"
                        + "plugins:[pascal.taie.analysis.pta.ProgressCountersPlugin];");
    }

    @Test
    void countersMatchTheSolvedGraphAndIntervalZeroLogsNothing() {
        solve("0");
        assertTrue(ProgressCountersPlugin.graphEdges > 0, "the program has call edges");
        assertEquals(ProgressCountersPlugin.graphEdges, ProgressCountersPlugin.csCallEdges,
                "the call edge counter counts each edge the call graph holds once");
        assertTrue(ProgressCountersPlugin.iterations >= ProgressCountersPlugin.graphEdges,
                "every call edge is one work list entry");
        assertEquals(0, ProgressCountersPlugin.progressLines);
        assertEquals(ProgressCountersPlugin.phases, ProgressCountersPlugin.waves,
                "one wave per phase, as the plugin bumped");
    }

    @Test
    void pluginCountersKeepWhatIsSet() {
        ProgressCounters counters = new ProgressCounters();
        assertEquals(0, counters.getPendingEntries());
        assertEquals(0, counters.getWaves());
        counters.setPendingEntries(5);
        counters.addWave();
        counters.addWave();
        assertEquals(5, counters.getPendingEntries());
        assertEquals(2, counters.getWaves());
    }

    @Test
    void negativeIntervalIsRefused() {
        RuntimeException e = assertThrows(RuntimeException.class, () -> solve("-1"));
        Throwable cause = e;
        while (cause != null && !(cause instanceof IllegalArgumentException
                && String.valueOf(cause.getMessage()).contains("progress-interval"))) {
            cause = cause.getCause();
        }
        assertNotNull(cause, "refused for the negative progress-interval: " + e);
    }
}
