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

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A method sends its callers only the exceptions new to its uncaught set.
 */
public class ExceptionFreshFanOutTest {

    /**
     * The second throw statement of {@code thrower} throws an object that
     * is already uncaught: nothing goes out to {@code main} again, so no
     * drained entry finds its exceptions all known.
     */
    @Test
    void knownUncaughtObjectIsNotSentAgain() {
        CounterReader.emptyDiffs = -1;
        CounterReader.mainUncaught = null;
        Tests.testPTA(false, "exception", "ExceptionThrownTwice",
                "plugins:[" + CounterReader.class.getName() + "]");
        assertEquals(0, CounterReader.emptyDiffs,
                "an entry brought only exceptions its statement already had");
        assertEquals(List.of("java.lang.RuntimeException"), CounterReader.mainUncaught,
                "the thrown object did not reach main");
    }

    /**
     * Reads the work counters of the exception analysis after the solve.
     */
    public static class CounterReader implements Plugin {

        static long emptyDiffs = -1;

        /**
         * The types of the objects that {@code main} does not catch.
         */
        static List<String> mainUncaught;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            emptyDiffs = ExceptionAnalysisAccess.of(solver).emptyDiffs;
            mainUncaught = solver.getCallGraph().reachableMethods()
                    .filter(m -> m.getMethod().getName().equals("main"))
                    .flatMap(m -> m.<CSMethodThrowResult>getResult(
                            ExceptionAnalysis.class.getName()).stream())
                    .flatMap(r -> r.mayThrowUncaught().stream())
                    .map(o -> o.getObject().getType().getName())
                    .toList();
        }
    }
}
