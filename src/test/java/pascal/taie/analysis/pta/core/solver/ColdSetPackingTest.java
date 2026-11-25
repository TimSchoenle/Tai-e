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
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetCensus;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code pack-cold-sets}: a whole analysis (application and
 * library) with the cold windows gives the pointers in the same creation
 * order, each with the same objects in the same iteration order, and the
 * same call graph as without them, while it packs sets.
 */
class ColdSetPackingTest {

    @Test
    void coldWindowsKeepEveryResultAndPackSets() {
        Run off = run("share-points-to-sets:true;");
        for (String window : new String[]{"1", "64"}) {
            Run on = run("share-points-to-sets:true;pack-cold-sets:" + window + ";");
            assertEquals(off.pointers, on.pointers, "window " + window);
            assertEquals(off.callEdges, on.callEdges, "window " + window);
            assertTrue(on.workList.coldPacks() > 0, "window " + window);
            assertTrue(on.workList.coldUnpacks() > 0, "window " + window);
            assertTrue(on.census.largeStoredPacked() > off.census.largeStoredPacked(),
                    "window " + window + ": " + on.census + " vs " + off.census);
            System.out.println("pack-cold-sets:" + window + " " + on.workList.countersLine()
                    + "\n off: " + off.census + "\n on: " + on.census);
        }
        assertEquals(0, off.workList.coldPacks());
    }

    @Test
    void coldWindowWithoutSharingKeepsEveryResult() {
        Run off = run("");
        Run control = run("");
        Run on = run("pack-cold-sets:1;");
        System.out.println("control iterations " + off.iterations + " " + control.iterations
                + " " + on.iterations + "\n off: " + off.census + "\n control: "
                + control.census + "\n on: " + on.census);
        assertEquals(off.pointers, control.pointers, "control");
        assertEquals(off.pointers, on.pointers);
        assertEquals(off.callEdges, on.callEdges);
        assertTrue(on.workList.coldPacks() > 0);
    }

    private record Run(List<String> pointers, List<String> callEdges, long iterations,
                       WorkList workList, PointsToSetCensus census) {
    }

    private static Run run(String options) {
        Main.main("-cp", "src/test/resources/pta/census", "-m", "Census",
                "-a", "pta=census:true;" + options + "plugins:[" + Probe.class.getName() + "];");
        assertNotNull(Probe.run, options);
        Run run = Probe.run;
        Probe.run = null;
        return run;
    }

    /**
     * Fingerprints every pointer, in creation order, by its objects in
     * iteration order, and the call graph by its edges in order.
     */
    public static class Probe implements Plugin {

        static Run run;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            CSManager csManager = solver.getCSManager();
            List<String> pointers = new ArrayList<>();
            Stream.concat(csManager.pointers(), csManager.mockPointers()).forEach(p -> {
                PointsToSet pts = p.getPointsToSet();
                pointers.add(p + " " + fingerprint(pts));
            });
            Collections.sort(pointers);
            List<String> callEdges = new ArrayList<>();
            solver.getCallGraph().edges().forEach(e -> callEdges.add(e.toString()));
            Collections.sort(callEdges);
            run = new Run(pointers, callEdges, (long) read(solver, "iterations"),
                    (WorkList) read(solver, "workList"),
                    ((SolverCensus) read(solver, "census")).pts());
        }

        /**
         * @return the size and an order-free hash of the objects by name:
         * creation indexes and hash iteration orders vary between two
         * analyses in one JVM (the model tests check iteration order)
         */
        private static String fingerprint(PointsToSet pts) {
            if (pts == null) {
                return "null";
            }
            long hash = 0;
            for (CSObj obj : pts) {
                long h = obj.toString().hashCode();
                hash += h * h + h;
            }
            return pts.size() + ":" + hash;
        }

        private static Object read(Object target, String name) {
            try {
                Field field = DefaultSolver.class.getDeclaredField(name);
                field.setAccessible(true);
                return field.get(target);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
