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
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.flowgraph.ArrayIndexNode;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.graph.flowgraph.ObjectFlowGraph;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ReflectionTest {

    private static final String DIR = "reflection";

    @Test
    void testBasic() {
        Tests.testPTA(DIR, "GetMember");
    }

    @Test
    void testReflectionLog() {
        Tests.testPTA(DIR, "ReflectiveAction",
                "reflection-inference:null",
                "reflection-log:src/test/resources/pta/reflection/ReflectiveAction.log");
    }

    private static final String ARGS_EDGE_CHECK =
            "plugins:[" + ReflectiveArgsEdgeCheck.class.getName() + "]";

    /**
     * Object-flow edges from argument array elements to reflective callee
     * parameters, as the analysis derived them before the elements were
     * relayed through one pointer per argument variable: 4 arrays reach
     * the 6 reference parameters of the Method.invoke callees, 1 array the
     * 2 of the constructor.
     */
    private static final long ARGS_OFG_EDGES = 4 * 6 + 2;

    @Test
    void testReflectiveArgsMerge() {
        Tests.testPTA(DIR, "ReflectiveArgsMerge", ARGS_EDGE_CHECK);
        assertEquals(ARGS_OFG_EDGES, countArgsFlowEdges());
    }

    @Test
    void testReflectiveArgsMergeContextSensitive() {
        Tests.testPTA(DIR, "ReflectiveArgsMergeCS", "cs:1-call", ARGS_EDGE_CHECK);
    }

    @Test
    void testReflectiveArgsMergeVerified() {
        System.setProperty("px.reflargs.verify", "true");
        // check while the solver runs too, at every new points-to set
        System.setProperty("px.reflargs.verify.every", "0");
        try {
            Tests.testPTA(DIR, "ReflectiveArgsMerge", ARGS_EDGE_CHECK);
            Tests.testPTA(DIR, "ReflectiveArgsMergeCS", "cs:1-call", ARGS_EDGE_CHECK);
        } finally {
            System.clearProperty("px.reflargs.verify");
            System.clearProperty("px.reflargs.verify.every");
        }
    }

    private static long countArgsFlowEdges() {
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        ObjectFlowGraph ofg = pta.getObjectFlowGraph();
        return ofg.getNodes().stream()
                .filter(n -> n instanceof ArrayIndexNode)
                .flatMap(n -> ofg.getOutEdgesOf(n).stream())
                .filter(e -> e.kind() == FlowKind.PARAMETER_PASSING)
                .count();
    }

    /**
     * Test cases for Solar
     */
    @ParameterizedTest
    @ValueSource(strings = {
            "LazyHeapModeling",
            "ArgsRefine",
            "GetMethods",
            "UnknownMethodName"
    })
    void testSolar(String mainClass) {
        Tests.testPTA(DIR, mainClass, "reflection-inference:solar");
    }
}
