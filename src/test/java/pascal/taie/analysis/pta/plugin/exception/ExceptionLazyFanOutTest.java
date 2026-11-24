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
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A wave of uncaught exceptions takes one work-list item, whatever the
 * number of call edges it goes out over.
 */
public class ExceptionLazyFanOutTest {

    /**
     * The number of call sites of {@code thrower} in the fixture.
     */
    private static final int CALL_SITES = 12;

    @Test
    void waveOverManyEdgesTakesOneItem() {
        CounterReader.maxWorkListSize = -1;
        Tests.testPTA(false, "exception", "ExceptionManyCallers",
                "plugins:[" + CounterReader.class.getName() + "]");
        assertTrue(CounterReader.maxWorkListSize > 0, "no exception work recorded");
        assertTrue(CounterReader.maxWorkListSize < CALL_SITES,
                "the work-list held " + CounterReader.maxWorkListSize
                        + " items, one per call edge of the wave");
    }

    /**
     * Reads the work counters of the exception analysis after the solve.
     */
    public static class CounterReader implements Plugin {

        static int maxWorkListSize = -1;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            maxWorkListSize = ExceptionAnalysisAccess.of(solver).maxWorkListSize;
        }
    }
}
