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
import pascal.taie.World;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.New;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Options {@code log-statistics} and {@code release-solver-state}: the
 * first skips the statistics (and the context-insensitive points-to sets
 * they cache), the second releases the solver state that only the solve
 * reads before the plugins' onFinish; the call graph is the same either way.
 */
public class SolverStateOptionsTest {

    @Test
    void statisticsFillTheVarPointsToCacheByDefault() throws Exception {
        run("");
        assertFalse(cachedVarPointsTo().isEmpty());
    }

    @Test
    void skippedStatisticsLeaveTheVarPointsToCacheEmpty() throws Exception {
        run("log-statistics:false;");
        assertTrue(cachedVarPointsTo().isEmpty());
    }

    @Test
    void keepsSolverStateByDefault() {
        run("plugins:[" + Probe.class.getName() + "];");
        Set<String> edges = callEdges();
        List<String> pointers = Probe.pointerSummary;
        List<String> filtered = Probe.refiltered;
        assertSame(Probe.workListAtStart, Probe.workListAtFinish);
        assertTrue(Probe.memoCount > 0, "no type filter memo to release");
        assertTrue(Probe.filtersWithMemo > 0, "no type filter holding a memo");
        assertNull(Probe.addEdgeFailure);
        assertNull(Probe.mockAddEdgeFailure);
        assertNull(Probe.lateEdgeFailure);
        assertNull(Probe.latePointsToFailure);
        assertNull(Probe.lateCallEdgeFailure);
        assertNull(Probe.lateMethodFailure);
        Probe.lateCreateFailures.forEach((call, failure) ->
                assertNull(failure, call + " was refused without the release"));
        assertFalse(filtered.isEmpty(), "the reapplied type filters passed no object");
        run("release-solver-state:true;plugins:[" + Probe.class.getName() + "];");
        assertEquals(edges, callEdges());
        assertEquals(pointers, Probe.pointerSummary);
        assertEquals(filtered, Probe.refiltered);
    }

    @Test
    void releasesSolverStateBeforeOnFinish() {
        run("release-solver-state:true;plugins:[" + Probe.class.getName() + "];");
        assertNotNull(Probe.workListAtFinish);
        assertFalse(Probe.workListAtStart == Probe.workListAtFinish,
                "the work list was not replaced");
        assertEquals(0, Probe.memoCount);
        assertEquals(0, Probe.filtersWithMemo);
        assertTrue(Probe.addEdgeFailure instanceof IllegalStateException,
                "a new out edge was accepted after the release: " + Probe.addEdgeFailure);
        assertTrue(Probe.mockAddEdgeFailure instanceof IllegalStateException,
                "a mock pointer accepted a new out edge after the release: "
                        + Probe.mockAddEdgeFailure);
        assertTrue(Probe.lateEdgeFailure instanceof IllegalStateException,
                "the solver accepted an edge between pointers created after the release: "
                        + Probe.lateEdgeFailure);
        assertTrue(Probe.latePointsToFailure instanceof IllegalStateException,
                "the released work list accepted a points-to entry: "
                        + Probe.latePointsToFailure);
        assertTrue(Probe.lateCallEdgeFailure instanceof IllegalStateException,
                "the released work list accepted a call edge: "
                        + Probe.lateCallEdgeFailure);
        assertTrue(Probe.lateMethodFailure instanceof IllegalStateException,
                "the solver accepted a method after the release: "
                        + Probe.lateMethodFailure);
        for (RuntimeException e : List.of(Probe.lateEdgeFailure, Probe.latePointsToFailure,
                Probe.lateCallEdgeFailure, Probe.lateMethodFailure)) {
            assertTrue(e.getMessage().startsWith("the solver state was released"),
                    "not the release refusal: " + e);
        }
        assertEquals(List.of("addVarPointsTo(set)", "addVarPointsTo(csObj)",
                        "addVarPointsTo(obj)", "addPointsTo(obj)", "addEntryPoint",
                        "addStmts", "initializeClass"),
                List.copyOf(Probe.lateCreateFailures.keySet()));
        Probe.lateCreateFailures.forEach((call, failure) -> assertTrue(
                failure instanceof IllegalStateException
                        && failure.getMessage().startsWith("the solver state was released"),
                call + " was not refused by the release: " + failure));
        // a refused call creates no context-sensitive variable or object and
        // adds no entry method
        assertEquals(Probe.csCountsBeforeLateCreate, Probe.csCountsAfterLateCreate);
        assertTrue(Probe.memoRebuilt, "a reapplied type filter did not rebuild its memo");
        assertEquals(Probe.filterCount, Probe.memosAfterReapply);
    }

    private static void run(String options) {
        Main.main("-cp", "src/test/resources/pta/exception",
                "-m", "ExceptionNoneCaught",
                "-a", "pta=" + options);
    }

    private static PointerAnalysisResult result() {
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static Map<?, ?> cachedVarPointsTo() throws Exception {
        return (Map<?, ?>) read(result(), "varPointsTo");
    }

    private static Set<String> callEdges() {
        return result().getCallGraph().edges()
                .map(e -> e.getCallSite().getContainer().getSignature()
                        + " -> " + e.getCallee().getSignature())
                .collect(Collectors.toSet());
    }

    private static Object read(Object owner, String name) throws ReflectiveOperationException {
        Class<?> type = owner instanceof Class<?> c ? c : owner.getClass();
        Field field = type.getDeclaredField(name);
        field.setAccessible(true);
        return field.get(owner instanceof Class<?> ? null : owner);
    }

    /**
     * Records, at onStart and at onFinish, the solver state that
     * {@code release-solver-state} releases, and tries to add a duplicate
     * of an existing out edge at onFinish. At onStart it adds an edge
     * between two mock pointers; at onFinish it records a summary of every
     * pointer and reapplies a type filter to a points-to set.
     */
    public static class Probe implements Plugin {

        static Object workListAtStart;

        static Object workListAtFinish;

        static int memoCount;

        static int filtersWithMemo;

        static RuntimeException addEdgeFailure;

        static RuntimeException mockAddEdgeFailure;

        static RuntimeException lateEdgeFailure;

        static RuntimeException latePointsToFailure;

        static RuntimeException lateCallEdgeFailure;

        static RuntimeException lateMethodFailure;

        /**
         * The outcome of each late call that names a variable or object
         * without a context-sensitive element yet, and of the late entry
         * point, statements and class initialization.
         */
        static Map<String, RuntimeException> lateCreateFailures;

        static String csCountsBeforeLateCreate;

        static String csCountsAfterLateCreate;

        static List<String> pointerSummary;

        static List<String> refiltered;

        static boolean memoRebuilt;

        static int memosAfterReapply;

        static int filterCount;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            workListAtStart = readSolver("workList");
            workListAtFinish = null;
            memoCount = -1;
            filtersWithMemo = -1;
            addEdgeFailure = null;
            mockAddEdgeFailure = null;
            lateEdgeFailure = null;
            latePointsToFailure = null;
            lateCallEdgeFailure = null;
            lateMethodFailure = null;
            lateCreateFailures = null;
            csCountsBeforeLateCreate = null;
            csCountsAfterLateCreate = null;
            pointerSummary = null;
            refiltered = null;
            memoRebuilt = false;
            memosAfterReapply = -1;
            filterCount = -1;
            CSManager csManager = solver.getCSManager();
            Type object = solver.getTypeSystem().getClassType(ClassNames.OBJECT);
            Pointer from = csManager.getMockPointer(
                    () -> "probe source", "probe source", object);
            Pointer to = csManager.getMockPointer(
                    () -> "probe target", "probe target", object);
            solver.addPFGEdge(new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, from, to));
        }

        @Override
        public void onFinish() {
            try {
                workListAtFinish = readSolver("workList");
                memoCount = ((Map<?, ?>) read(TypeFilter.class, "memos")).size();
                int holding = 0;
                for (Object filter : ((Map<?, ?>) readSolver("typeFilters")).values()) {
                    if (read(filter, "memo") != null) {
                        ++holding;
                    }
                }
                filtersWithMemo = holding;
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
            CSManager csManager = solver.getCSManager();
            pointerSummary = Stream.concat(csManager.pointers(), csManager.mockPointers())
                    .map(p -> p + " out=" + p.getOutDegree()
                            + " pts=" + p.getObjects().size())
                    .sorted()
                    .toList();
            reapplyTypeFilters(csManager);
            // an edge of a kind other than OTHER: without the release, its
            // duplicate is refused and the graph stays unchanged
            PointerFlowEdge existing = csManager.pointers()
                    .flatMap(p -> p.getOutEdges().stream())
                    .filter(e -> e.kind() != FlowKind.OTHER)
                    .findFirst()
                    .orElseThrow();
            addEdgeFailure = addDuplicate(existing);
            PointerFlowEdge mockEdge = csManager.mockPointers()
                    .flatMap(p -> p.getOutEdges().stream())
                    .findFirst()
                    .orElseThrow();
            mockAddEdgeFailure = addDuplicate(mockEdge);
            addLateWork(csManager);
        }

        /**
         * Gives the solver new work after its fixed point: an edge between
         * two pointers created now (their out-edge dedup state was never
         * released), a points-to entry and a call edge.
         */
        private void addLateWork(CSManager csManager) {
            Type object = solver.getTypeSystem().getClassType(ClassNames.OBJECT);
            Pointer from = csManager.getMockPointer(
                    () -> "late source", "late source", object);
            Pointer to = csManager.getMockPointer(
                    () -> "late target", "late target", object);
            lateEdgeFailure = attempt(() -> solver.addPFGEdge(
                    new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, from, to)));
            CSObj obj = csManager.getObjects().iterator().next();
            latePointsToFailure = attempt(() -> solver.addPointsTo(to, obj));
            Edge<CSCallSite, CSMethod> callEdge = solver.getCallGraph().edges()
                    .findFirst().orElseThrow();
            lateCallEdgeFailure = attempt(() -> solver.addCallEdge(callEdge));
            CSMethod reachable = solver.getCallGraph().reachableMethods()
                    .findFirst().orElseThrow();
            lateMethodFailure = attempt(() -> solver.addCSMethod(reachable));
            addLateCreatingWork(csManager, to, obj, reachable);
        }

        /**
         * Gives the solver late work that names a variable and an object of
         * a method the analysis never reached, so no context-sensitive
         * variable or object exists for them yet; and a late entry point (a
         * reachable method that is no entry method, no parameter objects),
         * an empty statement list and a class that was never initialized and
         * has no class initializer. Records each outcome and the numbers of
         * context-sensitive variables, objects and entry methods before and
         * after.
         */
        private void addLateCreatingWork(CSManager csManager, Pointer to, CSObj obj,
                                         CSMethod reachable) {
            Set<JMethod> reached = solver.getCallGraph().reachableMethods()
                    .map(CSMethod::getMethod)
                    .collect(Collectors.toSet());
            New alloc = World.get().getClassHierarchy().allClasses()
                    .flatMap(c -> c.getDeclaredMethods().stream())
                    .filter(m -> !m.isAbstract() && !m.isNative() && !reached.contains(m))
                    .flatMap(m -> m.getIR().getStmts().stream())
                    .filter(s -> s instanceof New)
                    .map(s -> (New) s)
                    .filter(s -> csManager.getCSVarsOf(s.getLValue()).isEmpty())
                    .findFirst()
                    .orElseThrow();
            Var var = alloc.getLValue();
            Obj newObj = solver.getHeapModel().getObj(alloc);
            Context empty = solver.getContextSelector().getEmptyContext();
            @SuppressWarnings("unchecked")
            Set<JClass> initialized = (Set<JClass>) readSolver("initializedClasses");
            JClass uninitialized = World.get().getClassHierarchy().allClasses()
                    .filter(c -> !initialized.contains(c) && c.getClinit() == null
                            && (c.getSuperClass() == null
                            || initialized.contains(c.getSuperClass())))
                    .findFirst()
                    .orElseThrow();
            Set<JMethod> entries = solver.getCallGraph().entryMethods()
                    .map(CSMethod::getMethod)
                    .collect(Collectors.toSet());
            JMethod lateEntry = reached.stream()
                    .filter(m -> !entries.contains(m))
                    .findFirst()
                    .orElseThrow();
            csCountsBeforeLateCreate = csCounts(csManager);
            Map<String, RuntimeException> failures = Maps.newLinkedHashMap();
            failures.put("addVarPointsTo(set)", attempt(() -> solver.addVarPointsTo(
                    empty, var, solver.makePointsToSet())));
            failures.put("addVarPointsTo(csObj)", attempt(() -> solver.addVarPointsTo(
                    empty, var, obj)));
            failures.put("addVarPointsTo(obj)", attempt(() -> solver.addVarPointsTo(
                    empty, var, empty, newObj)));
            failures.put("addPointsTo(obj)", attempt(() -> solver.addPointsTo(
                    to, empty, newObj)));
            failures.put("addEntryPoint", attempt(() -> solver.addEntryPoint(
                    new EntryPoint(lateEntry, EmptyParamProvider.get()))));
            failures.put("addStmts", attempt(() -> solver.addStmts(reachable, List.of())));
            failures.put("initializeClass", attempt(() -> solver.initializeClass(uninitialized)));
            csCountsAfterLateCreate = csCounts(csManager);
            lateCreateFailures = failures;
        }

        private String csCounts(CSManager csManager) {
            return "variables=" + csManager.getCSVars().size()
                    + " objects=" + csManager.getObjects().size()
                    + " entryMethods=" + solver.getCallGraph().entryMethods().count();
        }

        private static RuntimeException attempt(Runnable work) {
            try {
                work.run();
                return null;
            } catch (RuntimeException e) {
                return e;
            }
        }

        /**
         * Applies every type filter of the solver to the largest points-to
         * set (ties by pointer name), and records the passed objects per
         * guard type and whether every filter holds a memo again.
         */
        private void reapplyTypeFilters(CSManager csManager) {
            try {
                Pointer input = csManager.pointers()
                        .min(Comparator.comparingInt((Pointer p) -> -p.getObjects().size())
                                .thenComparing(Pointer::toString))
                        .orElseThrow();
                PointerFlowEdge edge = new PointerFlowEdge(FlowKind.OTHER, input, input);
                List<String> passed = new ArrayList<>();
                boolean allHoldMemo = true;
                Map<?, ?> filters = (Map<?, ?>) readSolver("typeFilters");
                for (Map.Entry<?, ?> entry : filters.entrySet()) {
                    TypeFilter filter = (TypeFilter) entry.getValue();
                    filter.apply(edge, input.getPointsToSet()).objects()
                            .forEach(o -> passed.add(entry.getKey() + " passes " + o));
                    allHoldMemo &= read(filter, "memo") != null;
                }
                filterCount = filters.size();
                refiltered = passed.stream().sorted().toList();
                memoRebuilt = allHoldMemo;
                memosAfterReapply = ((Map<?, ?>) read(TypeFilter.class, "memos")).size();
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        private static RuntimeException addDuplicate(PointerFlowEdge existing) {
            Pointer source = existing.source();
            try {
                source.addEdge(new PointerFlowEdge(
                        existing.kind(), source, existing.target()));
                return null;
            } catch (RuntimeException e) {
                return e;
            }
        }

        private Object readSolver(String name) {
            try {
                return read(solver, name);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
