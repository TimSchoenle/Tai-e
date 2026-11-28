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
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetCensus;
import pascal.taie.analysis.pta.pts.PointsToSetInterner;
import pascal.taie.ir.exp.Var;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Options {@code pack-cold-sets} (the interner's window over sole-held
 * sets) and {@code pack-cold-deltas} (the work list's window over merged
 * pending deltas): a whole analysis (application and library) with either
 * or both windows gives every pointer the same objects, every variable the
 * same objects, the same call graph (context-sensitive and
 * context-insensitive edges) and the same reachable methods as without
 * them, while each option packs only its own sets. Pointers and objects
 * are compared by name, free of order: two analyses in one JVM differ in
 * creation indexes, hash iteration orders and the iteration count even
 * with the options off. The model tests check poll order and iteration
 * order. A run keeps only names and counters, not the solver's state, so
 * that several runs fit the test heap.
 */
class ColdSetPackingTest {

    @Test
    void coldWindowsKeepEveryResultAndPackSets() {
        Run off = run("share-points-to-sets:true;");
        for (String window : new String[]{"1", "64"}) {
            Run on = run("share-points-to-sets:true;pack-cold-sets:" + window
                    + ";pack-cold-deltas:" + window + ";");
            assertSameResults(off, on, "window " + window);
            assertTrue(on.coldPacks > 0, "window " + window);
            assertTrue(on.coldUnpacks > 0, "window " + window);
            assertTrue(on.solePacks > 0, "window " + window);
            assertTrue(on.census.largeStoredPacked() > off.census.largeStoredPacked(),
                    "window " + window + ": " + on.census + " vs " + off.census);
            System.out.println("pack-cold-sets/deltas:" + window + " " + on.counters
                    + "\n off: " + off.census + "\n on: " + on.census);
        }
        assertEquals(0, off.coldPacks);
        assertEquals(0, off.solePacks);
    }

    /**
     * Each option alone packs only its own sets and keeps every result:
     * {@code pack-cold-deltas} the work list's merged pending deltas,
     * {@code pack-cold-sets} the interner's sole-held sets.
     */
    @Test
    void eachColdOptionPacksOnlyItsOwnSets() {
        Run off = run("share-points-to-sets:true;");
        Run deltas = run("share-points-to-sets:true;pack-cold-deltas:64;");
        assertSameResults(off, deltas, "pack-cold-deltas");
        assertTrue(deltas.coldPacks > 0, deltas.counters);
        assertTrue(deltas.coldUnpacks > 0, deltas.counters);
        assertEquals(0, deltas.solePacks);
        Run sets = run("share-points-to-sets:true;pack-cold-sets:64;");
        assertSameResults(off, sets, "pack-cold-sets");
        assertTrue(sets.solePacks > 0, sets.census.toString());
        assertEquals(0, sets.coldPacks, sets.counters);
        assertEquals(0, sets.coldUnpacks, sets.counters);
    }

    /**
     * Option {@code pack-pending-deltas}: packed pending deltas, of which
     * many merges that add nothing are answered on the packed words, give
     * every pointer the same objects and the same call graph as unpacked
     * deltas.
     */
    @Test
    void packedPendingDeltasKeepEveryResult() {
        Run off = run("share-points-to-sets:true;pack-pending-deltas:false;");
        Run on = run("share-points-to-sets:true;pack-pending-deltas:true;");
        assertSameResults(off, on, "pack-pending-deltas");
        assertEquals(0, off.packedUnchangedMerges);
        assertTrue(on.packedUnchangedMerges > 1000, on.counters);
        System.out.println("pack-pending-deltas " + on.counters);
    }

    @Test
    void coldWindowWithoutSharingKeepsEveryResult() {
        Run off = run("");
        Run control = run("");
        Run on = run("pack-cold-deltas:1;");
        System.out.println("control iterations " + off.iterations + " " + control.iterations
                + " " + on.iterations + "\n off: " + off.census + "\n control: "
                + control.census + "\n on: " + on.census);
        assertEquals(off.pointers, control.pointers, "control");
        assertSameResults(off, on, "pack-cold-deltas without sharing");
        assertTrue(on.coldPacks > 0);
    }

    private static void assertSameResults(Run expected, Run actual, String what) {
        assertEquals(expected.pointers, actual.pointers, what + ": pointers");
        assertEquals(expected.vars, actual.vars, what + ": variables");
        assertEquals(expected.callEdges, actual.callEdges, what + ": call edges");
        assertEquals(expected.ciCallEdges, actual.ciCallEdges, what + ": ci call edges");
        assertEquals(expected.reachable, actual.reachable, what + ": reachable methods");
    }

    private record Run(List<String> pointers, List<String> vars, List<String> callEdges,
                       List<String> ciCallEdges, List<String> reachable, long iterations,
                       long coldPacks, long coldUnpacks, long packedUnchangedMerges,
                       String counters, PointsToSetCensus census, long solePacks) {
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
     * Fingerprints every pointer by its objects, every variable by the
     * objects of all its contexts, and the call graph by its edges (with and
     * without contexts) and its reachable methods, all sorted by name.
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
            Map<Var, Set<Obj>> varObjects = Maps.newMap();
            Stream.concat(csManager.pointers(), csManager.mockPointers()).forEach(p -> {
                PointsToSet pts = p.getPointsToSet();
                pointers.add(p + " " + fingerprint(pts));
                if (p instanceof CSVar csVar) {
                    Set<Obj> objects = varObjects.computeIfAbsent(
                            csVar.getVar(), k -> Sets.newHybridSet());
                    if (pts != null) {
                        for (CSObj obj : pts) {
                            objects.add(obj.getObject());
                        }
                    }
                }
            });
            Collections.sort(pointers);
            List<String> vars = new ArrayList<>();
            varObjects.forEach((var, objects) -> vars.add(var.getMethod() + "/"
                    + var.getName() + " " + fingerprint(objects)));
            Collections.sort(vars);
            List<String> callEdges = new ArrayList<>();
            Set<String> ciEdgeSet = Sets.newSet();
            solver.getCallGraph().edges().forEach(e -> {
                callEdges.add(e.toString());
                ciEdgeSet.add(e.getKind() + " " + e.getCallSite().getCallSite()
                        + " -> " + e.getCallee().getMethod());
            });
            Collections.sort(callEdges);
            List<String> ciCallEdges = new ArrayList<>(ciEdgeSet);
            Collections.sort(ciCallEdges);
            List<String> reachable = new ArrayList<>();
            solver.getCallGraph().reachableMethods().forEach(m -> reachable.add(m.toString()));
            Collections.sort(reachable);
            WorkList workList = (WorkList) read(solver, "workList");
            run = new Run(pointers, vars, callEdges, ciCallEdges, reachable,
                    (long) read(solver, "iterations"),
                    workList.coldPacks(), workList.coldUnpacks(),
                    workList.packedUnchangedMerges(), workList.countersLine(),
                    ((SolverCensus) read(solver, "census")).pts(),
                    read(solver, "interner") instanceof PointsToSetInterner interner
                            ? interner.solePacks() : 0);
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

        /**
         * @return the size and an order-free hash of the objects by name
         */
        private static String fingerprint(Set<Obj> objects) {
            long hash = 0;
            for (Obj obj : objects) {
                long h = obj.toString().hashCode();
                hash += h * h + h;
            }
            return objects.size() + ":" + hash;
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
