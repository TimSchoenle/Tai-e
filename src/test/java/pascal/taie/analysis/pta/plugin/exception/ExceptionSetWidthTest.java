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
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.SetEx;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An exception set is as wide as the number of distinct exception objects
 * that exception analysis has seen, however high the global indexes of the
 * objects are, also once more throwable objects exist than the global
 * indexer reserves low indexes for.
 */
public class ExceptionSetWidthTest {

    /**
     * More throwable objects than the 2048 low indexes the global
     * {@link CSObj} indexer reserves for them.
     */
    private static final int THROWABLES = 2100;

    /**
     * Other objects created first, so that throwable objects past the
     * reserved range get high global indexes.
     */
    private static final int OTHER_OBJECTS = 50_000;

    @Test
    void setWidthFollowsTheNumberOfExceptionObjects() {
        Tests.testPTA(false, "exception", "ExceptionCircle",
                "plugins:[" + WidthProbe.class.getName() + "]");
        int bound = (THROWABLES + Long.SIZE - 1) / Long.SIZE;
        assertTrue(WidthProbe.lastGlobalIndex / Long.SIZE + 1 > bound,
                "the last throwable object did not get a high global index: "
                        + WidthProbe.lastGlobalIndex);
        assertTrue(WidthProbe.wordsOfLast <= bound,
                "a set holding one of " + THROWABLES + " exception objects has "
                        + WidthProbe.wordsOfLast + " words, more than " + bound);
        // a set that grows one element at a time doubles its words
        assertTrue(WidthProbe.wordsOfAll <= 2 * bound,
                "a set holding all " + THROWABLES + " exception objects has "
                        + WidthProbe.wordsOfAll + " words, more than " + 2 * bound);
    }

    /**
     * Creates the objects before the solve starts and measures the sets the
     * exception analysis of the solver creates.
     */
    public static class WidthProbe implements Plugin {

        private static final Descriptor DESC = () -> "ExceptionSetWidthTest";

        static int lastGlobalIndex;

        static int wordsOfLast;

        static int wordsOfAll;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            CSManager csManager = solver.getCSManager();
            Context ctx = solver.getContextSelector().getEmptyContext();
            Type object = solver.getTypeSystem().getClassType("java.lang.Object");
            Type exception = solver.getTypeSystem().getClassType("java.lang.RuntimeException");
            HeapModel heapModel = solver.getHeapModel();
            for (int i = 0; i < OTHER_OBJECTS; ++i) {
                csManager.getCSObj(ctx, heapModel.getMockObj(DESC, "other" + i, object));
            }
            List<CSObj> thrown = new ArrayList<>();
            for (int i = 0; i < THROWABLES; ++i) {
                thrown.add(csManager.getCSObj(ctx,
                        heapModel.getMockObj(DESC, "thrown" + i, exception)));
            }
            Supplier<SetEx<CSObj>> factory = ExceptionAnalysisAccess.setFactory(solver);
            SetEx<CSObj> all = factory.get();
            thrown.forEach(all::add);
            SetEx<CSObj> last = factory.get();
            last.add(thrown.get(THROWABLES - 1));
            lastGlobalIndex = thrown.get(THROWABLES - 1).getIndex();
            wordsOfLast = ExceptionAnalysisAccess.words(last);
            wordsOfAll = ExceptionAnalysisAccess.words(all);
        }
    }
}
