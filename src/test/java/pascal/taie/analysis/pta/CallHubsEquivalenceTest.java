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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code call-hubs} (px/s116 re-keyed B, owner S116-P9) gives the
 * same results as the solver without hubs: the CI call edges, the CS call
 * edges as node edges with their kinds, the reachable methods and CS
 * methods, and the points-to set of every variable and every CS variable.
 * The order of the solver's facts differs (accepted), so it is not
 * compared. Every call-edge callback sees its edge in both edge views, and
 * a call site's view grows by one edge per callback, as without hubs; the
 * views of every call site and CS method agree with their sizes and
 * random access.
 */
public class CallHubsEquivalenceTest {

    /**
     * Checks each call-edge callback against the edge views and keeps the
     * solver's hub counters.
     */
    public static class HubWatcher implements Plugin {

        static final List<String> VIOLATIONS = new ArrayList<>();

        static String counters = "";

        private final Map<CSCallSite, Integer> seen = new HashMap<>();

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            seen.clear();
        }

        @Override
        public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
            CSCallSite site = edge.getCallSite();
            int count = seen.merge(site, 1, Integer::sum);
            if (!site.getEdges().contains(edge)) {
                VIOLATIONS.add("site view lacks " + edge);
            }
            if (!edge.getCallee().getEdges().contains(edge)) {
                VIOLATIONS.add("callee view lacks " + edge);
            }
            if (site.getEdges().size() != count) {
                VIOLATIONS.add("site " + site + " shows " + site.getEdges().size()
                        + " edges at its callback " + count);
            }
        }

        @Override
        public void onFinish() {
            solver.getCallGraph().reachableMethods().forEach(m -> {
                List<Edge<CSCallSite, CSMethod>> iterated = new ArrayList<>();
                m.getEdges().forEach(iterated::add);
                List<Edge<CSCallSite, CSMethod>> indexed = new ArrayList<>();
                for (int i = 0; i < m.getEdgeCount(); ++i) {
                    indexed.add(m.getEdge(i));
                }
                List<Edge<CSCallSite, CSMethod>> streamed = m.getEdges().stream().toList();
                if (!iterated.equals(indexed) || !iterated.equals(streamed)
                        || iterated.size() != m.getEdges().size()) {
                    VIOLATIONS.add("callee views of " + m + " disagree");
                }
                solver.getCallGraph().getCallSitesIn(m).forEach(site -> {
                    int n = 0;
                    for (Edge<CSCallSite, CSMethod> e : site.getEdges()) {
                        ++n;
                        if (!site.getEdges().contains(e) || !e.getCallee().getEdges().contains(e)) {
                            VIOLATIONS.add("edge views disagree on " + e);
                        }
                    }
                    if (n != site.getEdges().size()) {
                        VIOLATIONS.add("site view size of " + site);
                    }
                });
            });
            counters = solver instanceof DefaultSolver d ? d.callHubsLine() : "";
        }
    }

    @AfterEach
    void clear() {
        HubWatcher.VIOLATIONS.clear();
        HubWatcher.counters = "";
    }

    public record Snapshot(Set<String> edges, List<String> csEdges, Set<String> reached,
                    Set<String> csReached, Map<String, Set<String>> pointsTo,
                    Map<String, Set<String>> csPointsTo, List<String> violations,
                    String counters) {
    }

    public static Snapshot run(String dir, String main, String cs, List<String> more) {
        return run(dir, main, cs, more, List.of());
    }

    /**
     * @param plugins further plugin classes, beside {@link HubWatcher}
     */
    public static Snapshot run(String dir, String main, String cs, List<String> more,
                               List<Class<? extends Plugin>> plugins) {
        String names = plugins.stream().map(c -> "," + c.getName())
                .collect(Collectors.joining());
        List<String> opts = new ArrayList<>(List.of("cs:" + cs,
                "plugins:[" + HubWatcher.class.getName() + names + "]"));
        opts.addAll(more);
        HubWatcher.VIOLATIONS.clear();
        Tests.testPTA(false, dir, main, opts.toArray(new String[0]));
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        CallGraph<Invoke, JMethod> callGraph = pta.getCallGraph();
        Set<String> edges = callGraph.edges()
                .map(e -> e.getKind() + " " + e.getCallSite().getContainer()
                        + "[" + e.getCallSite().getIndex() + "] -> " + e.getCallee())
                .collect(Collectors.toCollection(TreeSet::new));
        // a multiset: two edges of other classes (e.g. lambda edges of two
        // sources) between the same nodes print alike
        List<String> csEdges = pta.getCSCallGraph().edges()
                .map(e -> e.getKind() + " " + e.getCallSite().getContext() + ":"
                        + e.getCallSite().getCallSite().getContainer() + "["
                        + e.getCallSite().getCallSite().getIndex() + "] -> " + e.getCallee()
                        + " " + e.getClass().getSimpleName())
                .sorted()
                .toList();
        Set<String> reached = callGraph.reachableMethods().map(JMethod::toString)
                .collect(Collectors.toCollection(TreeSet::new));
        Set<String> csReached = pta.getCSCallGraph().reachableMethods().map(Object::toString)
                .collect(Collectors.toCollection(TreeSet::new));
        Map<String, Set<String>> pointsTo = new TreeMap<>();
        for (Var var : pta.getVars()) {
            pointsTo.put(var.getMethod() + "/" + var.getName(),
                    pta.getPointsToSet(var).stream().map(Object::toString)
                            .collect(Collectors.toCollection(TreeSet::new)));
        }
        Map<String, Set<String>> csPointsTo = new TreeMap<>();
        for (CSVar csVar : pta.getCSVars()) {
            csPointsTo.put(csVar.getContext() + ":" + csVar.getVar().getMethod() + "/"
                            + csVar.getVar().getName(),
                    csVar.getPointsToSet() == null ? Set.of()
                            : csVar.getPointsToSet().objects().map(Object::toString)
                            .collect(Collectors.toCollection(TreeSet::new)));
        }
        return new Snapshot(edges, csEdges, reached, csReached, pointsTo, csPointsTo,
                List.copyOf(HubWatcher.VIOLATIONS), HubWatcher.counters);
    }

    public static void assertSameResults(Snapshot off, Snapshot on, String what) {
        assertEquals(List.of(), off.violations(), what + ": views without hubs");
        assertEquals(List.of(), on.violations(), what + ": views with hubs");
        assertEquals(off.edges(), on.edges(), what + ": CI call edges");
        assertEquals(off.csEdges(), on.csEdges(), what + ": CS call edges");
        assertEquals(off.reached(), on.reached(), what + ": reachable methods");
        assertEquals(off.csReached(), on.csReached(), what + ": reachable CS methods");
        assertEquals(off.pointsTo(), on.pointsTo(), what + ": points-to sets");
        assertEquals(off.csPointsTo(), on.csPointsTo(), what + ": CS points-to sets");
    }

    /**
     * @param more further options separated by {@code ;}, or empty
     */
    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "hubs | HubJoin | ci |", "hubs | HubJoin | 1-call |", "hubs | HubJoin | 2-obj |",
            "blocks | Blocks | ci |", "blocks | Blocks | 1-call |",
            "blocks | Blocks | 2-call |", "blocks | Blocks | 1-obj |",
            "blocks | Blocks | 2-obj |", "blocks | Blocks | 2-type |",
            "blocks | SharedCallee | 1-obj |", "blocks | SharedCallee | ci |",
            "blocks | SharedCallee | 1-call |",
            "lambda | LambdaMix | 2-obj |", "lambda | LambdaMix | 1-call |",
            "lambda | LambdaSharedReceiver | 1-obj |", "lambda | LambdaSharedReceiver | 1-call |",
            "lambda | LambdaSharedTargets | 1-obj |", "lambda | LambdaReceiver | 2-obj |",
            "lambda | LambdaSelfReceiver | 2-obj |", "lambda | Streams | 1-obj |",
            "lambda | LambdaInstanceMethod | 1-call |", "lambda | LambdaConstructor | 1-call |",
            "lambda | LambdaConstructor | ci |", "lambda | LambdaStaticMethod | 1-call |",
            "lambda | LambdaContexts | 2-obj |", "lambda | LambdaRedundantEdge | 1-call |",
            "basic | Interface | ci |", "basic | Interface | 2-obj |",
            "basic | Dispatch | 1-call |", "basic | Dispatch | 2-obj |",
            "getters | Getters | ci | trivial-getters:true",
            "getters | Getters | 1-call | trivial-getters:true",
            "blocks | Blocks | 2-obj | share-points-to-sets:true;pack-cold-sets:4;"
                    + "pack-cold-deltas:4",
            "blocks | Blocks | 1-call | share-points-to-sets:true;pack-cold-sets:4;"
                    + "pack-cold-deltas:4",
            "blocks | Blocks | 1-call | call-batching:verify",
            "misc | Zipper | 2-obj | advanced:zipper",
            "misc | Zipper | 2-obj | advanced:scaler",
            "reflection | ReflectiveAction | 1-call | reflection-inference:null;"
                    + "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log"})
    void hubsChangeNoResult(String dir, String main, String cs, String more) {
        List<String> extra = more == null ? List.of() : List.of(more.split(";"));
        Snapshot off = run(dir, main, cs, extra);
        List<String> withHubs = new ArrayList<>(extra);
        withHubs.add("call-hubs:true");
        Snapshot on = run(dir, main, cs, withHubs);
        String what = dir + " " + main + " " + cs + " " + extra;
        assertSameResults(off, on, what);
        System.out.println("call hubs " + what + ": " + on.counters());
        assertEquals(off.csEdges().size(), counter(on.counters(), "cs_edges"),
                what + ": the CS edge counter counts announced pairs: " + on.counters());
    }

    /**
     * HubJoin under 1-call: the three contexts of s.id(x) reach the same
     * three callee nodes, so one context makes the hub and the two others
     * join it late; the joiners get every target (CS edges) and the union of
     * the arguments back through the return relay (points-to sets), as
     * without hubs, and the stored entries are fewer than the CS edges.
     */
    @Test
    void lateJoinersShareTheHub() {
        Snapshot on = run("hubs", "HubJoin", "1-call", List.of("call-hubs:true"));
        String c = on.counters();
        System.out.println("call hubs HubJoin 1-call: " + c);
        assertEquals(List.of(), on.violations());
        assertTrue(counter(c, "hubs") >= 2, c);
        assertTrue(counter(c, "joins") >= counter(c, "hubs") + 2, c);
        assertTrue(counter(c, "stored") < counter(c, "cs_edges"), c);
        Snapshot off = run("hubs", "HubJoin", "1-call", List.of());
        assertSameResults(off, on, "HubJoin 1-call");
        // Echo.id returns its parameter: under 1-call its one context gets
        // the arguments of all three contexts of call(), so every context's
        // result holds at least those three objects
        long fullResults = on.csPointsTo().entrySet().stream()
                .filter(e -> e.getKey().contains("<HubJoin: java.lang.Object main(")
                        || e.getKey().contains("java.lang.Object call(java.lang.Object)>/"))
                .filter(e -> e.getValue().stream().filter(o -> o.contains("NewObj")
                        && o.contains("HubJoin: void main")).count() >= 3)
                .count();
        assertTrue(fullResults >= 3, "results with the three arguments: " + fullResults);
    }

    /**
     * HubCap: one call site links twenty node sets of two, one after the
     * other. The first sixteen become hubs (DefaultSolver.HUB_REFS_MAX), the
     * nodes of every later set become stored call edges, and the results
     * are those without hubs.
     */
    @Test
    void sitesBeyondTheHubCapStoreTheirEdges() {
        Snapshot on = run("hubs", "HubCap", "ci", List.of("call-hubs:true"));
        String c = on.counters();
        System.out.println("call hubs HubCap ci: " + c);
        assertEquals(16, counter(c, "hubs"), c);
        assertTrue(counter(c, "direct_links") >= 4, c);
        Snapshot off = run("hubs", "HubCap", "ci", List.of());
        assertSameResults(off, on, "HubCap ci");
        assertEquals(off.csEdges().size(), counter(c, "cs_edges"), c);
    }

    /**
     * HubIgnored: hubs whose targets include ignored library methods (and
     * one hub of ignored targets only) pass no argument to and take no
     * return from an ignored target, as without hubs.
     */
    @ParameterizedTest
    @CsvSource({"ci", "1-call", "1-obj"})
    void ignoredTargetsInsideAHub(String cs) {
        Snapshot on = run("hubs", "HubIgnored", cs, List.of("call-hubs:true"));
        String c = on.counters();
        System.out.println("call hubs HubIgnored " + cs + ": " + c);
        assertTrue(counter(c, "hubs") >= 3, c);
        Snapshot off = run("hubs", "HubIgnored", cs, List.of());
        assertSameResults(off, on, "HubIgnored " + cs);
    }

    /**
     * Adds every plain edge again through {@link Solver#addCallEdge} when it
     * is announced: the call site refuses an edge it already has, stored or
     * in a hub, so no edge is stored or announced twice.
     */
    public static class EdgeReAdder implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
            if (edge.getClass() == Edge.class) {
                solver.addCallEdge(new Edge<>(edge.getKind(), edge.getCallSite(),
                        edge.getCallee()));
            }
        }
    }

    @ParameterizedTest
    @CsvSource({"HubJoin, 1-call", "HubJoin, ci", "HubCap, ci", "HubIgnored, 1-obj"})
    void plainEdgesAddedAgainAreRefused(String main, String cs) {
        List<Class<? extends Plugin>> readd = List.of(EdgeReAdder.class);
        Snapshot on = run("hubs", main, cs, List.of("call-hubs:true"), readd);
        String c = on.counters();
        assertTrue(counter(c, "hubs") >= 1, c);
        Snapshot off = run("hubs", main, cs, List.of(), readd);
        assertSameResults(off, on, main + " " + cs + " re-added");
        assertEquals(off.csEdges().size(), counter(c, "cs_edges"), c);
    }

    public static long counter(String line, String name) {
        Matcher m = Pattern.compile("(?:^| )" + name + "=(\\d+)").matcher(line);
        assertTrue(m.find(), name + " in " + line);
        return Long.parseLong(m.group(1));
    }
}
