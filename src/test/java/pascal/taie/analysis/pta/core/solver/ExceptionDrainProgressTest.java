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
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The exception analysis reports its drain on the solver's progress
 * counters, and runs the solver's progress check inside its drain.
 */
class ExceptionDrainProgressTest {

    @Test
    void exceptionDrainBumpsCountersAndRunsTheProgressCheck() {
        Tests.testPTA(false, "exception", "ExceptionManyCallers",
                "plugins:[" + DrainProbe.class.getName() + "]");
        assertTrue(DrainProbe.drained > 0, "the exception analysis drained entries");
        assertTrue(DrainProbe.waves > 0, "the exception analysis queued waves");
        assertTrue(DrainProbe.edges > 0, "the waves visited call edges");
        assertEquals(DrainProbe.drained, DrainProbe.pendingAtCheck.size(),
                "a check mask of 0 runs the progress check at every drained entry");
        assertTrue(DrainProbe.pendingAtCheck.stream().allMatch(p -> p > 0),
                "each check sees the entry it drains as pending");
        assertEquals(0, DrainProbe.pendingAtFinish,
                "no entry is pending after the drains");
    }

    /**
     * Replaces the solver's progress check by one that records the pending
     * count at every drained entry.
     */
    public static class DrainProbe implements Plugin {

        static List<Long> pendingAtCheck = List.of();

        static long drained = -1;

        static long waves = -1;

        static long edges = -1;

        static long pendingAtFinish = -1;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            ProgressCounters counters = solver.getProgressCounters();
            List<Long> recorded = new ArrayList<>();
            pendingAtCheck = recorded;
            counters.setProgressCheck(
                    () -> recorded.add(counters.getPendingEntries()), 0);
        }

        @Override
        public void onFinish() {
            ProgressCounters counters = solver.getProgressCounters();
            drained = counters.getEntriesDrained();
            waves = counters.getWaves();
            edges = counters.getEdgesVisited();
            pendingAtFinish = counters.getPendingEntries();
        }
    }
}
