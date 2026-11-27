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

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.Counter;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.EdgeClass;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code call-block-probe} (px/s116 L0) only counts: a solve with the
 * probe off and one with it on give the same solver events in the same
 * order ({@link SolverOrderRecorder}), the same call edges, reachable
 * methods and points-to sets of every variable; and the probe counts every
 * call edge of its classes.
 */
public class CallBlockProbeEquivalenceTest {

    private static final String PLUGINS = "plugins:["
            + SolverOrderRecorder.class.getName() + ","
            + ProbeReader.class.getName() + "]";

    /** Keeps the probe of the last solve. */
    public static class ProbeReader implements Plugin {

        static volatile CallBlockProbe probe;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            probe = solver.getCallBlockProbe();
        }
    }

    /**
     * The probe holds the object indexer of its CS manager, so a kept probe
     * keeps the whole solve and its World reachable for the rest of the
     * test JVM (the fork sweep ran out of its 2G heap); drop it after each
     * case.
     */
    @AfterEach
    void dropProbe() {
        ProbeReader.probe = null;
    }

    private record Snapshot(List<String> events, Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo) {
    }

    private static Snapshot run(String dir, String main, String cs, String mode,
                                String... more) {
        List<String> opts = new ArrayList<>(List.of("cs:" + cs,
                "call-block-probe:" + mode, PLUGINS));
        opts.addAll(List.of(more));
        // the probe of the previous solve would keep that solve while this one runs
        ProbeReader.probe = null;
        Tests.testPTA(false, dir, main, opts.toArray(new String[0]));
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        CallGraph<Invoke, JMethod> callGraph = pta.getCallGraph();
        Set<String> edges = callGraph.edges()
                .map(e -> e.getKind() + " " + e.getCallSite().getContainer()
                        + "[" + e.getCallSite().getIndex() + "] -> " + e.getCallee())
                .collect(Collectors.toCollection(TreeSet::new));
        Set<String> reached = callGraph.reachableMethods()
                .map(JMethod::toString)
                .collect(Collectors.toCollection(TreeSet::new));
        Map<String, Set<String>> pointsTo = new TreeMap<>();
        for (Var var : pta.getVars()) {
            pointsTo.put(var.getMethod() + "/" + var.getName(),
                    pta.getPointsToSet(var).stream().map(Object::toString)
                            .collect(Collectors.toCollection(TreeSet::new)));
        }
        return new Snapshot(List.copyOf(SolverOrderRecorder.EVENTS), edges, reached, pointsTo);
    }

    @ParameterizedTest
    @CsvSource({
            "blocks, Blocks, 1-call", "blocks, Blocks, 1-obj", "blocks, Blocks, ci",
            "lambda, LambdaMix, 2-obj", "lambda, LambdaSharedReceiver, 1-obj",
            "lambda, LambdaConstructor, 1-call", "lambda, LambdaStaticMethod, 1-call",
            "basic, Interface, 2-obj"})
    void probeChangesNoResultAndNoOrder(String dir, String main, String cs) {
        Snapshot off = run(dir, main, cs, "none");
        assertNull(ProbeReader.probe, "the probe is off by default value none");
        for (String mode : List.of("p1", "p1b")) {
            Snapshot on = run(dir, main, cs, mode);
            assertNotNull(ProbeReader.probe, mode);
            assertTrue(off.events().size() > 0, "the solve records events");
            assertEquals(off.events(), on.events(), mode + ": solver events in order");
            assertEquals(off.edges(), on.edges(), mode + ": call edges");
            assertEquals(off.reached(), on.reached(), mode + ": reachable methods");
            assertEquals(off.pointsTo(), on.pointsTo(), mode + ": points-to sets");
            assertEdgesOffered(ProbeReader.probe);
        }
    }

    @ParameterizedTest
    @CsvSource({"reflection, ReflectiveAction"})
    void reflectiveEdgesAreCounted(String dir, String main) {
        String[] log = {"reflection-inference:null",
                "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log"};
        Snapshot off = run(dir, main, "1-call", "none", log);
        Snapshot on = run(dir, main, "1-call", "p1b", log);
        assertEquals(off.events(), on.events(), "solver events in order");
        assertEquals(off.edges(), on.edges(), "call edges");
        assertEquals(off.pointsTo(), on.pointsTo(), "points-to sets");
        CallBlockProbe probe = ProbeReader.probe;
        assertTrue(probe.count(EdgeClass.REFLECTIVE, Counter.EDGES) > 0, probe.line());
        assertEdgesOffered(probe);
    }

    @ParameterizedTest
    @CsvSource({"1-call"})
    void equalReceiverDiffsOfTwoContextsShareABlock(String cs) {
        run("blocks", "Blocks", cs, "p1b");
        CallBlockProbe probe = ProbeReader.probe;
        // shape.area() in drawAll under its two call-site contexts
        assertTrue(probe.count(EdgeClass.PLAIN, Counter.P1_HITS) > 0, probe.line());
        assertTrue(probe.count(EdgeClass.PLAIN, Counter.P1_BLOCKS)
                < probe.count(EdgeClass.PLAIN, Counter.BATCHES), probe.line());
        assertTrue(probe.phase1RuleCost(EdgeClass.PLAIN)
                <= probe.phase1Cost(EdgeClass.PLAIN), probe.line());
        for (EdgeClass c : List.of(EdgeClass.LAMBDA_BOUND, EdgeClass.LAMBDA_UNBOUND,
                EdgeClass.LAMBDA_STATIC, EdgeClass.LAMBDA_NEW)) {
            assertTrue(probe.count(c, Counter.EDGES) > 0, c + ": " + probe.line());
        }
    }

    /**
     * Every call edge the call graph took is in some batch: per class, the
     * edges are at most the summed distinct callee nodes of the batches.
     */
    private static void assertEdgesOffered(CallBlockProbe probe) {
        for (EdgeClass c : EdgeClass.values()) {
            assertTrue(probe.count(c, Counter.EDGES) <= probe.count(c, Counter.DIRECT),
                    c + ": " + probe.line());
        }
    }
}
