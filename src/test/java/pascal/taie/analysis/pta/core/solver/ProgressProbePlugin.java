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

import pascal.taie.analysis.pta.plugin.Plugin;

import java.util.List;

/**
 * Probe for {@link ProgressLineTest}: bumps the plugin-side progress
 * counters before the solve starts, optionally replaces the progress check
 * of the solver, and records the counters when the solve starts and ends.
 */
public class ProgressProbePlugin implements Plugin {

    /**
     * No replacement of the progress check.
     */
    static final long NO_HOOK = -1;

    /**
     * The progress interval in nanoseconds the probe installs, with a check
     * at every work list entry; {@link #NO_HOOK} keeps the solver's own.
     */
    static volatile long hookIntervalNanos = NO_HOOK;

    static volatile long countersAtStart = -1;

    static volatile long iterations = -1;

    static volatile long csCallEdges = -1;

    static volatile long graphEdges = -1;

    static volatile long progressLines = -1;

    /**
     * The solved call graph's edges, sorted.
     */
    static volatile List<String> callEdges = List.of();

    /**
     * Each context-sensitive variable with its sorted points-to set, sorted.
     */
    static volatile List<String> pointsTo = List.of();

    private Solver solver;

    static void clear() {
        callEdges = List.of();
        pointsTo = List.of();
        countersAtStart = -1;
        iterations = -1;
        csCallEdges = -1;
        graphEdges = -1;
        progressLines = -1;
    }

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        ProgressCounters counters = solver.getProgressCounters();
        counters.setPendingEntries(7);
        counters.addWave();
        if (hookIntervalNanos != NO_HOOK) {
            ((DefaultSolver) solver).setProgressCheckForTesting(0, hookIntervalNanos);
        }
    }

    @Override
    public void onStart() {
        ProgressCounters counters = solver.getProgressCounters();
        countersAtStart = counters.getPendingEntries() + counters.getWaves();
    }

    @Override
    public void onFinish() {
        DefaultSolver s = (DefaultSolver) solver;
        iterations = s.getIterations();
        csCallEdges = s.getNumberOfCSCallEdges();
        graphEdges = s.getCallGraph().edges().count();
        progressLines = s.getProgressLines();
        callEdges = s.getCallGraph().edges()
                .map(Object::toString)
                .sorted()
                .toList();
        pointsTo = s.getCSManager().getCSVars().stream()
                .filter(v -> v.getPointsToSet() != null)
                .map(v -> v + " -> " + v.getPointsToSet().objects()
                        .map(Object::toString)
                        .sorted()
                        .toList())
                .sorted()
                .toList();
    }
}
