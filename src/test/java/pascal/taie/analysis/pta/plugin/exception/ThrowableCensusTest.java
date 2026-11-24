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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager.ThrowableCensus;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.language.type.Type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The census counts every throwable object that gets a global index and
 * notes when the first one falls outside the reserved range.
 */
public class ThrowableCensusTest {

    @Test
    void countsThrowableObjectsAndNotesTheExceededBudget() {
        Tests.testPTA(false, "exception", "ExceptionCircle",
                "plugins:[" + CensusProbe.class.getName() + "]");
        ThrowableCensus before = CensusProbe.before;
        ThrowableCensus filled = CensusProbe.filled;
        ThrowableCensus past = CensusProbe.past;
        assertFalse(before.budgetExceeded());
        assertEquals(before.budget(), filled.throwableObjects());
        assertFalse(filled.budgetExceeded(), "exceeded with every reserved index in use");
        assertEquals(before.budget() + 1, past.throwableObjects());
        assertTrue(past.budgetExceeded());
        assertTrue(CensusProbe.atFinish.throwableObjects() >= past.throwableObjects());
        assertEquals(past.budgetExceededAfterMillis(),
                CensusProbe.atFinish.budgetExceededAfterMillis());
    }

    /**
     * Fills the reserved range with throwable objects before the solve
     * starts, then creates one more.
     */
    public static class CensusProbe implements Plugin {

        private static final Descriptor DESC = () -> "ThrowableCensusTest";

        static ThrowableCensus before;

        static ThrowableCensus filled;

        static ThrowableCensus past;

        static ThrowableCensus atFinish;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            MapBasedCSManager csManager = (MapBasedCSManager) solver.getCSManager();
            Context ctx = solver.getContextSelector().getEmptyContext();
            Type exception = solver.getTypeSystem().getClassType("java.lang.RuntimeException");
            before = csManager.getThrowableCensus();
            HeapModel heapModel = solver.getHeapModel();
            int missing = before.budget() - before.throwableObjects();
            for (int i = 0; i < missing; ++i) {
                csManager.getCSObj(ctx, heapModel.getMockObj(DESC, "thrown" + i, exception));
            }
            filled = csManager.getThrowableCensus();
            csManager.getCSObj(ctx, heapModel.getMockObj(DESC, "past", exception));
            past = csManager.getThrowableCensus();
        }

        @Override
        public void onFinish() {
            atFinish = ((MapBasedCSManager) solver.getCSManager()).getThrowableCensus();
        }
    }
}
