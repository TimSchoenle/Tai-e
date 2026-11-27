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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code call-batching} (px/s116 L-B) changes no result and no
 * order: a solve with {@code per-object}, one with {@code batched} and one
 * with {@code verify} (which also checks every context the selector reports
 * independent of the receiver against the per-object selection) give the
 * same solver events in the same order ({@link SolverOrderRecorder}), the
 * same call edges, reachable methods and points-to sets of every variable.
 */
public class CallBatchingEquivalenceTest {

    private static final String PLUGINS = "plugins:["
            + SolverOrderRecorder.class.getName() + "]";

    private record Snapshot(List<String> events, Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo) {
    }

    private static Snapshot run(String dir, String main, String cs, String mode,
                                List<String> more) {
        List<String> opts = new ArrayList<>(List.of("cs:" + cs,
                "call-batching:" + mode, PLUGINS));
        opts.addAll(more);
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

    /**
     * @param more further options separated by {@code ;}, or empty
     */
    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "blocks | Blocks | ci |", "blocks | Blocks | 1-call |",
            "blocks | Blocks | 2-call |", "blocks | Blocks | 1-obj |",
            "blocks | Blocks | 2-type |",
            // several receiver objects per callee at one call site
            "blocks | SharedCallee | 1-obj |", "blocks | SharedCallee | ci |",
            "lambda | LambdaMix | 2-obj |", "lambda | LambdaSharedReceiver | 1-call |",
            "lambda | LambdaConstructor | ci |",
            "basic | Interface | ci |", "basic | Dispatch | 1-call |",
            "basic | Dispatch | 2-obj |",
            "getters | Getters | ci | trivial-getters:true",
            "getters | Getters | 1-call | trivial-getters:true",
            "blocks | Blocks | 2-obj | share-points-to-sets:true;pack-cold-sets:4",
            "blocks | Blocks | 1-call | share-points-to-sets:true;pack-cold-sets:4",
            "misc | Zipper | 2-obj | advanced:zipper",
            "misc | Zipper | 2-obj | advanced:scaler",
            "reflection | ReflectiveAction | 1-call | reflection-inference:null;"
                    + "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log"})
    void batchingChangesNoResultAndNoOrder(String dir, String main, String cs, String more) {
        List<String> extra = more == null ? List.of() : Arrays.asList(more.split(";"));
        Snapshot off = run(dir, main, cs, "per-object", extra);
        assertTrue(off.events().size() > 0, "the solve records events");
        for (String mode : List.of("batched", "verify")) {
            Snapshot on = run(dir, main, cs, mode, extra);
            assertEquals(off.events(), on.events(), mode + ": solver events in order");
            assertEquals(off.edges(), on.edges(), mode + ": call edges");
            assertEquals(off.reached(), on.reached(), mode + ": reachable methods");
            assertEquals(off.pointsTo(), on.pointsTo(), mode + ": points-to sets");
        }
    }
}
