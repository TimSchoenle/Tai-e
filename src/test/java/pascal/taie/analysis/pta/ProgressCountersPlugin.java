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

import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

/**
 * Records the solver's progress counters at the end of a solve, for
 * {@link ProgressCountersTest}, and bumps the plugin-side counters once
 * per phase.
 */
public class ProgressCountersPlugin implements Plugin {

    static volatile long iterations = -1;

    static volatile long csCallEdges = -1;

    static volatile long graphEdges = -1;

    static volatile long progressLines = -1;

    static volatile long phases = -1;

    static volatile long waves = -1;

    private Solver solver;

    private long phaseCount;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
    }

    @Override
    public void onPhaseFinish() {
        ++phaseCount;
        solver.getProgressCounters().addWave();
    }

    @Override
    public void onFinish() {
        DefaultSolver s = (DefaultSolver) solver;
        iterations = s.getIterations();
        csCallEdges = s.getNumberOfCSCallEdges();
        graphEdges = s.getCallGraph().edges().count();
        progressLines = s.getProgressLines();
        phases = phaseCount;
        waves = s.getProgressCounters().getWaves();
    }
}
