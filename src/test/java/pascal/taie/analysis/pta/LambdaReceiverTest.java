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
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A method reference whose receiver is a lambda object (fixture
 * {@code LambdaReceiver}) calls the lambda's target method, as a call of the
 * lambda's functional method would, with the arguments the method reference
 * passes, although the lambda object's type does not dispatch that method:
 * bound ({@code r1::run}), unbound ({@code Runnable::run} applied to the
 * lambda object), nested (a method reference of a method reference, and a
 * lambda calling a method reference), on a lambda object of
 * {@code altMetafactory} with a marker's default method, to static,
 * instance and constructor targets, and along a cycle of the points-to sets.
 */
public class LambdaReceiverTest {

    private static final String MAIN = "LambdaReceiver";

    private static final List<String> REACHED = List.of(
            "boundBody", "unboundBody", "nestedBody", "lambdaOfRefBody",
            "markBody", "markerSamBody",
            "boundArgSink", "boundReturnSink", "unboundArgSink", "unboundReturnSink",
            "staticBody", "holderBody", "ctorBody", "cycleBody");

    private static Set<String> reachedNames(String cs) {
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", MAIN,
                "-a", "pta=cs:" + cs + ";handle-invokedynamic:true;");
        PointerAnalysisResult result = World.get().getResult(PointerAnalysis.ID);
        CallGraph<Invoke, JMethod> callGraph = result.getCallGraph();
        System.out.println("[mr] cs=" + cs
                + " reached=" + callGraph.getNumberOfMethods()
                + " edges=" + callGraph.getNumberOfEdges()
                + " objects=" + result.getObjects().size());
        return callGraph.reachableMethods()
                .filter(m -> m.getDeclaringClass().getName().equals(MAIN))
                .map(JMethod::getName)
                .collect(Collectors.toSet());
    }

    @Test
    void methodReferencesOnLambdaObjectsReachTheirBodies() {
        for (String cs : List.of("ci", "1-obj", "1-call")) {
            Set<String> reached = reachedNames(cs);
            for (String name : REACHED) {
                assertTrue(reached.contains(name), cs + ": " + name + " unreached");
            }
        }
    }
}
