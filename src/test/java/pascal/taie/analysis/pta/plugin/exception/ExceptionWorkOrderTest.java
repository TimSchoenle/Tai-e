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
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.exp.Var;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The exception analysis hands caught objects to the solver in a fixed
 * order, and queues no work for an empty exception set.
 */
public class ExceptionWorkOrderTest {

    private static final String DIR = "exception";

    /**
     * Past the first handler more than eight objects are left; each handler
     * must still receive its objects in the order of their global indexes,
     * so two runs hand them over identically.
     */
    @Test
    void laterHandlersReceiveCaughtObjectsInGlobalIndexOrder() {
        List<Catch> first = run();
        List<Catch> second = run();
        assertEquals(describe(first), describe(second));
        int longestGroup = 0;
        int group = 0;
        for (int i = 0; i < first.size(); i++) {
            Catch current = first.get(i);
            if (i > 0 && first.get(i - 1).var() == current.var()) {
                group++;
                assertTrue(first.get(i - 1).index() < current.index(),
                        "out of global index order at " + i + ": " + describe(first));
            } else {
                group = 1;
            }
            longestGroup = Math.max(longestGroup, group);
        }
        assertTrue(longestGroup > 8,
                "no handler received more than eight objects: " + describe(first));
    }

    /**
     * A call edge into a method whose uncaught set is empty creates no
     * result for the caller: the empty set is not queued.
     */
    @Test
    void emptyUncaughtSetQueuesNothing() {
        Tests.testPTA(false, DIR, "ExceptionCaughtThenCalledBack",
                "plugins:[" + ResultRecorder.class.getName() + "]");
        assertFalse(ResultRecorder.methods.isEmpty(), "CalledBack.again was not reached");
        assertEquals(List.of(), ResultRecorder.methodsWithResult,
                "a method reached only by empty exception sets got a result");
    }

    private static List<Catch> run() {
        Tests.testPTA(false, DIR, "ExceptionTwoHandlers",
                "plugins:[" + CatchRecorder.class.getName() + "]");
        assertFalse(CatchRecorder.catches.isEmpty(), "no caught object recorded");
        return CatchRecorder.catches;
    }

    private static List<String> describe(List<Catch> catches) {
        return catches.stream().map(c -> c.var() + "@" + c.var().getMethod()
                + " <- " + c.obj()).toList();
    }

    private record Catch(Var var, String obj, int index) {
    }

    /**
     * Records, in call order, every object the exception analysis adds to
     * a variable.
     */
    public static class CatchRecorder implements Plugin {

        static List<Catch> catches;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            List<Catch> recorded = new ArrayList<>();
            catches = recorded;
            Solver real = solver;
            Solver recording = (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> {
                        if (isAddCSObj(method)) {
                            CSObj obj = (CSObj) args[2];
                            recorded.add(new Catch((Var) args[1], obj.toString(),
                                    obj.getIndex()));
                        }
                        try {
                            return method.invoke(real, args);
                        } catch (InvocationTargetException e) {
                            throw e.getCause();
                        }
                    });
            ExceptionAnalysisAccess.replaceSolver(solver, recording);
        }

        private static boolean isAddCSObj(Method method) {
            return method.getName().equals("addVarPointsTo")
                    && method.getParameterCount() == 3
                    && method.getParameterTypes()[2] == CSObj.class;
        }
    }

    /**
     * Records the CS methods of {@code CalledBack.again} and those of them
     * that hold an exception result.
     */
    public static class ResultRecorder implements Plugin {

        static List<String> methods;

        static List<String> methodsWithResult;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            List<CSMethod> again = solver.getCallGraph().reachableMethods()
                    .filter(m -> m.getMethod().getName().equals("again"))
                    .toList();
            methods = again.stream().map(CSMethod::toString).toList();
            methodsWithResult = again.stream()
                    .filter(m -> m.getResult(ExceptionAnalysis.class.getName()).isPresent())
                    .map(CSMethod::toString)
                    .toList();
        }
    }
}
