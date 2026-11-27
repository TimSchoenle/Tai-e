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

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.pts.PointsToSet;
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
 * The options of LambdaAnalysis that skip repeated work:
 * {@code lambda-edge-prefilter} (default on) changes no fact and no order:
 * the solver events, in order, equal those with the prefilter off;
 * {@code lambda-skip-repeated-call} (default off) keeps the fixpoint: the
 * call edges, reachable methods and points-to sets of every variable equal
 * those without it.
 */
class LambdaRepeatEquivalenceTest {

    /**
     * The facts of one solve: the solver events in order; the call edges,
     * reachable methods and points-to sets of variables without contexts;
     * and with contexts, the edges of the CS call graph and every CS
     * variable's points-to set, as sorted lines (a list, so lines that
     * print alike are not merged).
     */
    private record Snapshot(List<String> events, Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo, List<String> csEdges,
                            List<String> csPointsTo) {
    }

    private static Snapshot run(String main, String cs, String options) {
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", main,
                "-a", "pta=cs:" + cs + ";implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true;" + options
                        + "plugins:[" + SolverOrderRecorder.class.getName() + "];");
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
        List<String> csEdges = pta.getCSCallGraph().edges()
                .map(e -> e.getKind() + " " + e.getCallSite() + " -> " + e.getCallee())
                .sorted()
                .toList();
        List<String> csPointsTo = pta.getCSVars().stream()
                .map(v -> v + " -> " + pointsToText(v.getPointsToSet()))
                .sorted()
                .toList();
        return new Snapshot(List.copyOf(SolverOrderRecorder.EVENTS), edges, reached, pointsTo,
                csEdges, csPointsTo);
    }

    /**
     * @return the objects of {@code pts} as a sorted set text; an absent set
     * prints as empty.
     */
    private static String pointsToText(@Nullable PointsToSet pts) {
        if (pts == null) {
            return "[]";
        }
        return pts.objects().map(Object::toString)
                .collect(Collectors.toCollection(TreeSet::new)).toString();
    }

    @ParameterizedTest
    @CsvSource({
            "LambdaMix, 2-obj", "LambdaMix, 1-call", "LambdaSharedReceiver, 1-obj",
            "LambdaSharedTargets, 1-obj", "LambdaReceiver, 2-obj", "LambdaSelfReceiver, 2-obj",
            "Streams, 1-obj", "LambdaInstanceMethod, 1-call", "LambdaConstructor, 1-call",
            "LambdaStaticMethod, 1-call", "LambdaContexts, 2-obj",
            "LambdaRedundantEdge, 1-call"})
    void repeatOptionsKeepTheResult(String main, String cs) {
        Snapshot off = run(main, cs,
                "lambda-edge-prefilter:false;lambda-skip-repeated-call:false;");
        Snapshot prefilter = run(main, cs,
                "lambda-edge-prefilter:true;lambda-skip-repeated-call:false;");
        assertTrue(off.events().size() > 0, "the solve records events");
        assertEquals(off.events(), prefilter.events(), "prefilter: solver events in order");
        assertEquals(off.edges(), prefilter.edges(), "prefilter: call edges");
        assertEquals(off.reached(), prefilter.reached(), "prefilter: reachable methods");
        assertEquals(off.pointsTo(), prefilter.pointsTo(), "prefilter: points-to sets");
        assertEquals(off.csEdges(), prefilter.csEdges(), "prefilter: CS call edges");
        assertEquals(off.csPointsTo(), prefilter.csPointsTo(), "prefilter: CS points-to sets");
        Snapshot skip = run(main, cs,
                "lambda-edge-prefilter:true;lambda-skip-repeated-call:true;");
        assertEquals(off.edges(), skip.edges(), "skip: call edges");
        assertEquals(off.reached(), skip.reached(), "skip: reachable methods");
        assertEquals(off.pointsTo(), skip.pointsTo(), "skip: points-to sets");
        assertEquals(off.csEdges(), skip.csEdges(), "skip: CS call edges");
        assertEquals(off.csPointsTo(), skip.csPointsTo(), "skip: CS points-to sets");
    }
}
