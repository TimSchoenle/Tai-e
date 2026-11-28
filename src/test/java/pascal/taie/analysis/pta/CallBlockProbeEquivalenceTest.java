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
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.Counter;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.EdgeClass;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.IR;
import pascal.taie.ir.IRBuilder;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.NullType;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;

import java.lang.reflect.Field;
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
            + IrBuildGuard.class.getName() + ","
            + ProbeReader.class.getName() + "]";

    /** The class name of the probe; its nested classes start with it and {@code $}. */
    private static final String PROBE_CLASS = CallBlockProbe.class.getName();

    /**
     * Watches each IR the solve builds ({@link JMethod#getIR()} builds a
     * method's IR once): a build while a frame of {@link CallBlockProbe} (or
     * of a class nested in it) is on the stack is a violation, as the probe
     * must read no callee state, so it never builds an IR earlier than a
     * solve without it. Only the builds of the solve count: after it,
     * readers of the result build IRs of their own.
     */
    public static class IrBuildGuard implements Plugin {

        static volatile boolean solving;

        /** The IRs the current solve built. */
        static int builds;

        /** The methods whose IR was built under a probe frame. */
        static final List<String> VIOLATIONS = new ArrayList<>();

        @Override
        public void onFinish() {
            solving = false;
        }

        @Override
        public void onStart() {
            builds = 0;
            solving = true;
            World world = World.get();
            IRBuilder builder = world.getIRBuilder();
            if (!(builder instanceof RecordingIRBuilder)) {
                try {
                    // World sets its IR builder once; a test replaces it
                    Field field = World.class.getDeclaredField("irBuilder");
                    field.setAccessible(true);
                    field.set(world, new RecordingIRBuilder(builder));
                } catch (ReflectiveOperationException e) {
                    throw new IllegalStateException("cannot record the IR builds", e);
                }
            }
        }
    }

    /** An IR builder that checks the stack of each IR it builds during a solve. */
    private record RecordingIRBuilder(IRBuilder delegate) implements IRBuilder {

        @Override
        public IR buildIR(JMethod method) {
            if (IrBuildGuard.solving) {
                ++IrBuildGuard.builds;
                if (underProbeFrame()) {
                    synchronized (IrBuildGuard.VIOLATIONS) {
                        IrBuildGuard.VIOLATIONS.add(method.toString());
                    }
                }
            }
            return delegate.buildIR(method);
        }

        private static boolean underProbeFrame() {
            return StackWalker.getInstance().walk(frames -> frames
                    .map(StackWalker.StackFrame::getClassName)
                    .anyMatch(name -> name.equals(PROBE_CLASS)
                            || name.startsWith(PROBE_CLASS + "$")));
        }

        @Override
        public void buildAll(ClassHierarchy hierarchy) {
            delegate.buildAll(hierarchy);
        }
    }

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
        IrBuildGuard.solving = false;
        IrBuildGuard.builds = 0;
        synchronized (IrBuildGuard.VIOLATIONS) {
            IrBuildGuard.VIOLATIONS.clear();
        }
    }

    /**
     * @param irBuilds         the IRs the solve built
     * @param probeIrBuilds    the methods whose IR it built under a probe frame
     */
    private record Snapshot(List<String> events, Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo, int irBuilds,
                            List<String> probeIrBuilds) {
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
        List<String> probeIrBuilds;
        synchronized (IrBuildGuard.VIOLATIONS) {
            probeIrBuilds = List.copyOf(IrBuildGuard.VIOLATIONS);
            IrBuildGuard.VIOLATIONS.clear();
        }
        return new Snapshot(List.copyOf(SolverOrderRecorder.EVENTS), edges, reached, pointsTo,
                IrBuildGuard.builds, probeIrBuilds);
    }

    /**
     * Checks a solve with the probe on: it built IRs, none of them under a
     * probe frame, and every edge a batch claimed was polled.
     */
    private static void assertProbeQuiet(Snapshot on, String mode) {
        assertTrue(on.irBuilds() > 0, mode + ": the solve builds IRs");
        assertEquals(List.of(), on.probeIrBuilds(), mode + ": IRs built under the probe");
        CallBlockProbe probe = ProbeReader.probe;
        assertEquals(0, probe.pendingEdges(), mode + ": " + probe.line());
        assertTrue(probe.line().contains(" w_pending=0"), probe.line());
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
        for (String mode : List.of("p1", "p1b", "p1t")) {
            Snapshot on = run(dir, main, cs, mode);
            assertNotNull(ProbeReader.probe, mode);
            assertTrue(off.events().size() > 0, "the solve records events");
            assertProbeQuiet(on, mode);
            assertEquals(off.events(), on.events(), mode + ": solver events in order");
            assertEquals(off.edges(), on.edges(), mode + ": call edges");
            assertEquals(off.reached(), on.reached(), mode + ": reachable methods");
            assertEquals(off.pointsTo(), on.pointsTo(), mode + ": points-to sets");
            assertEdgesOffered(ProbeReader.probe);
        }
    }

    /**
     * The probe under the option {@code lambda-shared-edges}: a batch claims
     * the lambda edge the analysis hands to the solver, which carries the
     * shape of its source, so every claimed edge is polled; and the probe
     * changes no result and no order there either.
     */
    @ParameterizedTest
    @CsvSource({
            "lambda, LambdaSharedEdges, 1-obj", "lambda, LambdaSharedEdges, 2-obj",
            "lambda, LambdaSharedEdges, ci", "lambda, LambdaContexts, 2-obj",
            "lambda, LambdaSharedReceiver, 1-obj", "lambda, LambdaMix, 2-obj"})
    void probeClaimsTheSharedLambdaEdge(String dir, String main, String cs) {
        Snapshot off = run(dir, main, cs, "none", "lambda-shared-edges:true");
        assertTrue(off.events().size() > 0, "the solve records events");
        for (String mode : List.of("p1", "p1b", "p1t")) {
            Snapshot on = run(dir, main, cs, mode, "lambda-shared-edges:true");
            assertProbeQuiet(on, mode);
            assertEquals(off.events(), on.events(), mode + ": solver events in order");
            assertEquals(off.edges(), on.edges(), mode + ": call edges");
            assertEquals(off.reached(), on.reached(), mode + ": reachable methods");
            assertEquals(off.pointsTo(), on.pointsTo(), mode + ": points-to sets");
            assertEdgesOffered(ProbeReader.probe);
        }
    }

    /**
     * The probe on the batched call path (option {@code call-batching},
     * px/s116 L-B) on the fixtures of {@link CallBatchingEquivalenceTest}:
     * {@code p1t} with {@code batched} gives the same solver events in the
     * same order, call edges, reachable methods and points-to sets as the
     * probe off with {@code per-object}, and the same probe counts as
     * {@code p1t} with {@code per-object}: batched offers every receiver
     * object and claims the same fresh edges.
     *
     * @param more further options separated by {@code ;}, or empty
     */
    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "blocks | Blocks | ci |", "blocks | Blocks | 1-call |",
            "blocks | Blocks | 2-call |", "blocks | Blocks | 1-obj |",
            "blocks | Blocks | 2-type |",
            "blocks | SharedCallee | 1-obj |", "blocks | SharedCallee | ci |",
            "lambda | LambdaMix | 2-obj |", "lambda | LambdaSharedReceiver | 1-call |",
            "lambda | LambdaConstructor | ci |",
            "basic | Interface | ci |", "basic | Dispatch | 1-call |",
            "basic | Dispatch | 2-obj |",
            "getters | Getters | ci | trivial-getters:true",
            "getters | Getters | 1-call | trivial-getters:true",
            "blocks | Blocks | 2-obj | share-points-to-sets:true;pack-cold-sets:4;"
                    + "pack-cold-deltas:4",
            "blocks | Blocks | 1-call | share-points-to-sets:true;pack-cold-sets:4;"
                    + "pack-cold-deltas:4",
            "misc | Zipper | 2-obj | advanced:zipper",
            "misc | Zipper | 2-obj | advanced:scaler",
            "reflection | ReflectiveAction | 1-call | reflection-inference:null;"
                    + "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log"})
    void probeOnBatchedCallsChangesNoResultAndNoCount(String dir, String main, String cs,
                                                       String more) {
        List<String> extra = more == null ? List.of() : List.of(more.split(";"));
        Snapshot off = run(dir, main, cs, "none",
                withOption(extra, "call-batching:per-object"));
        assertTrue(off.events().size() > 0, "the solve records events");
        run(dir, main, cs, "p1t", withOption(extra, "call-batching:per-object"));
        String perObjectLine = ProbeReader.probe.line();
        Snapshot on = run(dir, main, cs, "p1t", withOption(extra, "call-batching:batched"));
        // not assertProbeQuiet: with advanced:zipper or scaler the
        // pre-analysis builds the IRs, so the main solve may build none
        assertEquals(List.of(), on.probeIrBuilds(), "IRs built under the probe");
        assertEquals(0, ProbeReader.probe.pendingEdges(), ProbeReader.probe.line());
        assertEquals(off.events(), on.events(), "solver events in order");
        assertEquals(off.edges(), on.edges(), "call edges");
        assertEquals(off.reached(), on.reached(), "reachable methods");
        assertEquals(off.pointsTo(), on.pointsTo(), "points-to sets");
        assertEquals(perObjectLine, ProbeReader.probe.line(), "probe counts");
        assertEdgesOffered(ProbeReader.probe);
    }

    private static String[] withOption(List<String> options, String option) {
        List<String> all = new ArrayList<>(options);
        all.add(option);
        return all.toArray(new String[0]);
    }

    @ParameterizedTest
    @CsvSource({"reflection, ReflectiveAction"})
    void reflectiveEdgesAreCounted(String dir, String main) {
        String[] log = {"reflection-inference:null",
                "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log"};
        Snapshot off = run(dir, main, "1-call", "none", log);
        for (String mode : List.of("p1b", "p1t")) {
            Snapshot on = run(dir, main, "1-call", mode, log);
            assertProbeQuiet(on, mode);
            assertEquals(off.events(), on.events(), mode + ": solver events in order");
            assertEquals(off.edges(), on.edges(), mode + ": call edges");
            assertEquals(off.pointsTo(), on.pointsTo(), mode + ": points-to sets");
            CallBlockProbe probe = ProbeReader.probe;
            assertTrue(probe.count(EdgeClass.REFLECTIVE, Counter.EDGES) > 0, probe.line());
            assertEdgesOffered(probe);
        }
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
     * Plain {@code W_TODAY} is the PFG edges processCallEdge adds for the
     * plain call edges, recounted here from the CS call graph: one per
     * argument of reference type when the call site's arguments match the
     * callee's parameters, and one per return variable of reference type
     * when the call site's result is of reference type (the default
     * propagate types), for a callee that is not ignored (an application
     * method under the tests' {@code only-app:true}).
     */
    @ParameterizedTest
    @CsvSource({"ci", "1-call", "2-obj"})
    void plainWeightsAreTheAddedParameterAndReturnEdges(String cs) {
        run("basic", "Call", cs, "p1t");
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        long argEdges = 0;
        long returnEdges = 0;
        for (Edge<CSCallSite, CSMethod> edge : pta.getCSCallGraph().edges().toList()) {
            JMethod callee = edge.getCallee().getMethod();
            if (!isPlain(edge) || !callee.isApplication()) {
                continue;
            }
            Invoke callSite = edge.getCallSite().getCallSite();
            InvokeExp invokeExp = callSite.getInvokeExp();
            if (invokeExp.getArgCount() == callee.getParamCount()) {
                argEdges += invokeExp.getArgs().stream()
                        .filter(arg -> isReference(arg.getType())).count();
            }
            Var lhs = callSite.getResult();
            if (lhs != null && isReference(lhs.getType())) {
                returnEdges += callee.getIR().getReturnVars().stream()
                        .filter(ret -> isReference(ret.getType())).count();
            }
        }
        CallBlockProbe probe = ProbeReader.probe;
        // the fixture passes two arguments to foo and takes its result
        assertTrue(argEdges > 0 && returnEdges > 0, argEdges + " " + returnEdges);
        assertEquals(argEdges + returnEdges, probe.count(EdgeClass.PLAIN, Counter.W_TODAY),
                probe.line());
    }

    /** @return whether the probe counts {@code edge} as {@link EdgeClass#PLAIN} */
    private static boolean isPlain(Edge<CSCallSite, CSMethod> edge) {
        CallKind kind = edge.getKind();
        return edge.getClass() == Edge.class && (kind == CallKind.VIRTUAL
                || kind == CallKind.INTERFACE || kind == CallKind.SPECIAL);
    }

    private static boolean isReference(Type type) {
        return type instanceof ReferenceType && !(type instanceof NullType);
    }

    /**
     * Every call edge the call graph took is in some batch: per class, the
     * edges are at most the summed distinct callee nodes of the batches; and
     * a callee node is fresh exactly when its batch makes a new edge, so the
     * fresh nodes are the edges.
     */
    private static void assertEdgesOffered(CallBlockProbe probe) {
        for (EdgeClass c : EdgeClass.values()) {
            assertTrue(probe.count(c, Counter.EDGES) <= probe.count(c, Counter.DIRECT),
                    c + ": " + probe.line());
            assertEquals(probe.count(c, Counter.EDGES), probe.count(c, Counter.FRESH),
                    c + " fresh: " + probe.line());
        }
    }
}
