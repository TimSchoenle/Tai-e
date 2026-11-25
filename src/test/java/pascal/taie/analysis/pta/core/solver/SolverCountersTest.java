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
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.TestElements;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.DelegatePointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.HybridBitSet;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The measurement counters of the solver: each counts what it names, and
 * none changes a result or the solver's order.
 */
public class SolverCountersTest {

    private static final int OBJECTS = 64;

    private final CSObj[] objs = TestElements.objects(OBJECTS);

    private final PointsToSetFactory factory =
            new PointsToSetFactory(TestElements.indexer(objs));

    private PointsToSet set(int from, int to) {
        PointsToSet set = factory.make();
        for (int i = from; i < to; ++i) {
            set.addObject(objs[i]);
        }
        return set;
    }

    @Test
    void workListCountsMergesThatAddNothing() {
        WorkList workList = new WorkList(factory, false, true);
        Pointer p = TestElements.pointer(0);
        workList.addEntry(p, set(0, 2));
        workList.addEntry(p, set(1, 2));
        workList.addEntry(p, set(2, 3));
        assertEquals(1, workList.mergesUnchanged());
        WorkList off = new WorkList(factory, false);
        off.addEntry(p, set(0, 2));
        off.addEntry(p, set(1, 2));
        assertEquals(0, off.mergesUnchanged());
    }

    @Test
    void workListCountsPolledAndDiffBits() {
        WorkList workList = new WorkList(factory, false, true);
        workList.recordPropagation(5, 0);
        workList.recordPropagation(3, 2);
        assertEquals(8, workList.polledBits());
        assertEquals(2, workList.diffBits());
        assertEquals(1, workList.emptyDiffPolls());
        WorkList off = new WorkList(factory, false, false);
        off.recordPropagation(5, 0);
        assertEquals(0, off.polledBits());
        assertEquals(0, off.emptyDiffPolls());
        assertFalse(off.countersLine().contains("polled_bits"));
        assertTrue(workList.countersLine().contains("empty_diff_polls=1"));
    }

    @Test
    void workListCountsPackedAndPendingBytes() {
        WorkList workList = new WorkList(factory, true, true);
        workList.addEntry(TestElements.pointer(0), set(0, OBJECTS));
        assertEquals(1, workList.packs());
        long packed = workList.packedBytes();
        assertTrue(packed > 16, "packed bytes " + packed);
        workList.addEntry(TestElements.pointer(1), set(0, 3));
        assertEquals(packed, workList.pendingFootprint()[0]);
        assertEquals(3, workList.pendingFootprint()[1]);
        workList.pollPointer();
        workList.takePolledDelta();
        assertEquals(0, workList.pendingFootprint()[0]);
        assertEquals(packed, workList.packedBytes());
    }

    /**
     * A delta of a set stored packed is a snapshot of its words by
     * reference: it is no packed copy, and the pending walk reports its
     * words apart from the copies.
     */
    @Test
    void workListCountsReferencedPendingBytesApartFromCopies() {
        WorkList workList = new WorkList(factory, true, true);
        PointsToSet source = set(0, OBJECTS);
        HybridBitSet<?> hybrid = (HybridBitSet<?>) ((DelegatePointsToSet) source).set;
        hybrid.packLarge();
        assertTrue(hybrid.isPackedLarge());
        workList.addEntry(TestElements.pointer(0), source);
        assertEquals(1, workList.packedByReference());
        assertEquals(0, workList.packedBytes());
        long[] pending = workList.pendingFootprint();
        assertEquals(0, pending[0]);
        assertEquals(16L + workList.packedReferenceBytes(), pending[2]);
        assertTrue(workList.countersLine().contains("pending_reference_bytes=" + pending[2]));
        workList.pollPointer();
        workList.takePolledDelta();
        assertEquals(0, workList.pendingFootprint()[2]);
    }

    @Test
    void objectCensusTellsLambdaObjectsFromOtherMockObjects() {
        MockObj lambda = new MockObj(() -> CSObjCensus.LAMBDA_DESCRIPTOR,
                "indy", null, null, true);
        assertEquals(CSObjCensus.KIND_LAMBDA, CSObjCensus.kindOf(lambda));
        assertEquals(CSObjCensus.KIND_MOCK, CSObjCensus.kindOf(objs[0].getObject()));
    }

    @Test
    void countsOnlyWithTheCensus() {
        run("src/test/resources/pta/lambda", "LambdaContexts",
                "cs:1-obj;implicit-entries:false;");
        for (int origin = 0; origin < Probe.adds.length; ++origin) {
            assertEquals(0, Probe.adds[origin], "origin " + origin);
        }
        assertEquals("", Probe.typeFilterLine);
        run("src/test/resources/pta/lambda", "LambdaContexts",
                "cs:1-obj;implicit-entries:false;census:true;share-points-to-sets:true;");
        assertTrue(Probe.adds[DefaultSolver.ORIGIN_INITIAL_FLOW] > 0, "no initial flow");
        assertTrue(Probe.adds[DefaultSolver.ORIGIN_FAN_OUT] > 0, "no fan-out");
        assertTrue(Probe.adds[DefaultSolver.ORIGIN_PROCESS_CALL] > 0, "no receiver flow");
        assertTrue(Probe.adds[DefaultSolver.ORIGIN_OTHER] > 0, "no other flow");
        assertTrue(Probe.polledBits >= Probe.diffBits && Probe.diffBits > 0,
                Probe.polledBits + " polled, " + Probe.diffBits + " diff");
        assertTrue(Probe.typeFilterLine.contains("type_tests="), Probe.typeFilterLine);
        assertTrue(Probe.countersLine.contains("copies_small_small="), Probe.countersLine);
        CSObjCensus objs = Probe.objs;
        assertNotNull(objs);
        long lambdas = objs.byKind()[CSObjCensus.KIND_LAMBDA];
        assertTrue(lambdas > 0, "no lambda object");
        assertTrue(objs.lambdaCapturing() > 0 && objs.lambdaCapturing() <= lambdas,
                objs.toString());
        assertTrue(objs.byKind()[CSObjCensus.KIND_NEW] > 0);
    }

    @Test
    void countersChangeNoResultAndNoOrder() {
        String options = "implicit-entries:false;cs:1-obj;share-points-to-sets:true;";
        run("src/test/resources/pta/lambda", "LambdaContexts", options);
        List<Long> pointers = Probe.pointers;
        List<Long> edges = Probe.edges;
        List<String> names = Probe.names;
        assertTrue(pointers.size() > 10, "too small: " + pointers.size());
        runCounting("src/test/resources/pta/lambda", "LambdaContexts", options);
        assertEquals(edges, Probe.edges);
        assertSamePointers(pointers, names, Probe.pointers);
    }

    /**
     * With the implicit entries, two runs in one JVM already differ in the
     * numbering of the IR's temporary variables and in the order of the
     * objects, counters or not; their call edges and the sizes of the
     * points-to sets agree.
     */
    @Test
    void countersChangeNoResultOnALargeProgram() {
        String options = "implicit-entries:true;share-points-to-sets:true;";
        run("src/test/resources/pta/lambda", "ImpreciseLambdas", options);
        List<Long> sizes = Probe.sizes;
        List<Long> edges = Probe.edges;
        assertTrue(sizes.size() > 10_000, "too small: " + sizes.size());
        runCounting("src/test/resources/pta/lambda", "ImpreciseLambdas", options);
        assertEquals(edges, Probe.edges);
        assertEquals(sizes, Probe.sizes);
    }

    private static void runCounting(String classPath, String main, String options) {
        System.setProperty(DefaultSolver.COUNTERS_PROPERTY, "true");
        try {
            run(classPath, main, options);
        } finally {
            System.clearProperty(DefaultSolver.COUNTERS_PROPERTY);
        }
        assertTrue(Probe.adds[DefaultSolver.ORIGIN_FAN_OUT] > 0, "counters were off");
    }

    private static void assertSamePointers(List<Long> expected, List<String> names,
                                           List<Long> actual) {
        int n = Math.min(expected.size(), actual.size());
        for (int i = 0; i < n; ++i) {
            if (!expected.get(i).equals(actual.get(i))) {
                throw new AssertionError("pointer " + i + " differs: " + names.get(i)
                        + " vs " + Probe.names.get(i));
            }
        }
        assertEquals(expected.size(), actual.size());
    }

    private static void run(String classPath, String main, String options) {
        Probe.objs = null;
        Main.main("-cp", classPath, "-m", main,
                "-a", "pta=" + options + "plugins:[" + Probe.class.getName() + "];");
    }

    /**
     * Records at onFinish the counters, and every pointer (in index order,
     * with its objects in iteration order) and call edge in the order the
     * solver made them.
     */
    public static class Probe implements Plugin {

        static long[] adds = new long[0];

        static String typeFilterLine = "";

        static String countersLine = "";

        static long polledBits;

        static long diffBits;

        static CSObjCensus objs;

        static List<Long> pointers = List.of();

        static List<Long> edges = List.of();

        static List<String> names = List.of();

        static List<Long> sizes = List.of();

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            DefaultSolver s = (DefaultSolver) solver;
            adds = new long[4];
            for (int origin = 0; origin < adds.length; ++origin) {
                adds[origin] = s.addsFrom(origin);
            }
            countersLine = s.countersLine();
            polledBits = s.getWorkListForCounters().polledBits();
            diffBits = s.getWorkListForCounters().diffBits();
            int at = countersLine.indexOf("; type filters ") + "; type filters ".length();
            int end = countersLine.indexOf(';', at);
            typeFilterLine = countersLine.substring(at, end < 0 ? countersLine.length() : end);
            SolverCensus census = census(s);
            objs = census == null ? null : census.objs();
            Indexer<CSObj> objects = solver.getCSManager().getObjectIndexer();
            List<Long> ps = new ArrayList<>();
            List<String> ns = new ArrayList<>();
            solver.getCSManager().pointers()
                    .sorted(Comparator.comparingInt(Pointer::getIndex))
                    .forEach(p -> {
                        ns.add(p.getIndex() + " " + p);
                        // not the name: the IR's temporary variables are
                        // numbered differently in each run of one JVM
                        long[] h = {31L * p.getIndex() + p.getClass().getName().hashCode()};
                        PointsToSet pts = p.getPointsToSet();
                        if (pts != null) {
                            pts.forEach(o -> h[0] = 31 * h[0] + objects.getIndex(o));
                        }
                        ps.add(h[0]);
                    });
            pointers = ps;
            names = ns;
            sizes = solver.getCSManager().pointers()
                    .map(p -> 31L * p.getClass().getName().hashCode()
                            + (p.getPointsToSet() == null ? -1 : p.getPointsToSet().size()))
                    .sorted().toList();
            // the call graph iterates its edges in no fixed order; the
            // indexes of the pointers and objects record the solver's order
            edges = solver.getCallGraph().edges()
                    .map(e -> (long) e.toString().hashCode()).sorted().toList();
        }

        private static SolverCensus census(DefaultSolver s) {
            try {
                java.lang.reflect.Field field = DefaultSolver.class.getDeclaredField("census");
                field.setAccessible(true);
                return (SolverCensus) field.get(s);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
