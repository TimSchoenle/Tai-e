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

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The option {@code lambda-shared-edges} (default off) stores one lambda call
 * edge per call site, callee and passing shape instead of one per source,
 * and keeps the fixpoint: the call edges, reachable methods, CS call graph
 * node edges and the points-to sets of every variable and CS variable equal
 * those without it.
 */
class LambdaSharedEdgesTest {

    /**
     * The facts of one solve. {@code csEdgeRows} lists the CS call edges as
     * stored (an edge per source prints like the others of its call site
     * and callee), {@code csEdges} the distinct node edges.
     */
    private record Snapshot(Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo, List<String> csEdgeRows,
                            Set<String> csEdges, List<String> csPointsTo) {
    }

    private static Snapshot run(String main, String cs, boolean shared) {
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", main,
                "-a", "pta=cs:" + cs + ";implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true;census:true;"
                        + "lambda-shared-edges:" + shared + ";");
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
            pointsTo.put(var.getMethod() + "/" + var.getName(), objects(pta, var));
        }
        List<String> csEdgeRows = pta.getCSCallGraph().edges()
                .map(e -> e.getKind() + " " + e.getCallSite() + " -> " + e.getCallee())
                .sorted()
                .toList();
        List<String> csPointsTo = pta.getCSVars().stream()
                .map(LambdaSharedEdgesTest::pointsToText)
                .sorted()
                .toList();
        return new Snapshot(edges, reached, pointsTo, csEdgeRows,
                new TreeSet<>(csEdgeRows), csPointsTo);
    }

    private static Set<String> objects(PointerAnalysisResult pta, Var var) {
        return pta.getPointsToSet(var).stream().map(Object::toString)
                .collect(Collectors.toCollection(TreeSet::new));
    }

    private static String pointsToText(CSVar v) {
        return v + " -> " + (v.getPointsToSet() == null ? "[]"
                : v.getPointsToSet().objects().map(Object::toString)
                .collect(Collectors.toCollection(TreeSet::new)).toString());
    }

    private static void assertSameFixpoint(Snapshot off, Snapshot on) {
        assertEquals(off.edges(), on.edges(), "call edges");
        assertEquals(off.reached(), on.reached(), "reachable methods");
        assertEquals(off.pointsTo(), on.pointsTo(), "points-to sets");
        assertEquals(off.csEdges(), on.csEdges(), "CS call graph node edges");
        assertEquals(off.csPointsTo(), on.csPointsTo(), "CS points-to sets");
        assertTrue(on.csEdgeRows().size() <= off.csEdgeRows().size(), "stored edges");
    }

    @ParameterizedTest
    @CsvSource({
            "LambdaMix, 2-obj", "LambdaMix, 1-call", "LambdaSharedReceiver, 1-obj",
            "LambdaSharedTargets, 1-obj", "LambdaReceiver, 2-obj", "LambdaSelfReceiver, 2-obj",
            "Streams, 1-obj", "LambdaInstanceMethod, 1-call", "LambdaConstructor, 1-call",
            "LambdaStaticMethod, 1-call", "LambdaContexts, 2-obj",
            "LambdaRedundantEdge, 1-call", "ImpreciseLambdas, 1-obj", "Args, 1-obj",
            "LambdaFieldBase, 1-obj", "LambdaDefaultMethod, 1-obj",
            "LambdaAddedInterfaces, 1-obj", "LambdaEnterMisses, 1-obj",
            "LambdaEnterSupertypes, 1-obj", "NativeModelWithLambda, 1-obj",
            "DispatchBugDueToLackOfSubclassCheck, 1-obj", "LambdaSharedEdges, 1-obj",
            "LambdaSharedEdges, 2-obj", "LambdaSharedEdges, ci"})
    void sharedEdgesKeepTheResult(String main, String cs) {
        Snapshot off = run(main, cs, false);
        Snapshot on = run(main, cs, true);
        System.out.println("[r4] " + main + " " + cs + " stored lambda-graph rows off="
                + off.csEdgeRows().size() + " on=" + on.csEdgeRows().size()
                + " node edges=" + off.csEdges().size());
        assertSameFixpoint(off, on);
        assertEquals(on.csEdges().size(), on.csEdgeRows().size(),
                "one stored edge per node edge with the option");
    }

    /**
     * The StateDefinition shape: three capturing sources call one CS callee
     * at one call site, two non-capturing method references one static
     * target. Each captured object reaches the lambda body's parameter, and
     * the option stores one edge for each pair instead of three and two.
     */
    @Test
    void capturedVariablesOfEverySourceReachTheSharedCallee() {
        Snapshot off = run("LambdaSharedEdges", "2-obj", false);
        Snapshot on = run("LambdaSharedEdges", "2-obj", true);
        assertSameFixpoint(off, on);
        assertEquals(3, off.csEdgeRows().size() - off.csEdges().size(),
                "source duplicates without the option: 2 capturing + 1 non-capturing");
        assertEquals(on.csEdges().size(), on.csEdgeRows().size(), "none with the option");
        Set<String> v = on.pointsTo().entrySet().stream()
                .filter(e -> e.getKey().contains("lambda$make$")
                        && e.getKey().endsWith("/v"))
                .flatMap(e -> e.getValue().stream())
                .collect(Collectors.toCollection(TreeSet::new));
        assertTrue(v.stream().anyMatch(o -> o.contains("First"))
                        && v.stream().anyMatch(o -> o.contains("Second"))
                        && v.stream().anyMatch(o -> o.contains("Third")),
                "the captured object of every source reaches the lambda body: " + v);
    }
}
