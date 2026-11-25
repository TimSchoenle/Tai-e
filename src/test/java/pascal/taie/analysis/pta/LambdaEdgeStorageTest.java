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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.callgraph.OtherEdge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.EdgeSource;
import pascal.taie.analysis.pta.core.cs.element.SourcedEdge;
import pascal.taie.util.collection.Maps;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Lambda call edges are held by their call site and callee without an edge
 * object: each read rebuilds an equal edge of the same class, with the same
 * hash code, in the same order, from both ends.
 */
public class LambdaEdgeStorageTest {

    private static final String LAMBDA_EDGE = "LambdaCallEdge";

    private static PointerAnalysisResult pta;

    @BeforeAll
    static void analyse() {
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", "LambdaContexts",
                "-a", "pta=cs:1-obj;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true");
        pta = World.get().getResult(PointerAnalysis.ID);
    }

    @Test
    void lambdaEdgesAreRebuiltOnEachRead() {
        List<CSCallSite> sites = pta.getCSCallGraph().edges()
                .filter(LambdaEdgeStorageTest::isLambdaEdge)
                .map(Edge::getCallSite)
                .distinct()
                .toList();
        assertTrue(sites.size() >= 4, "call sites with lambda edges: " + sites.size());
        int lambdaEdges = 0;
        for (CSCallSite site : sites) {
            List<Edge<CSCallSite, CSMethod>> first = List.copyOf(site.getEdges());
            List<Edge<CSCallSite, CSMethod>> second = List.copyOf(site.getEdges());
            assertEquals(first, second);
            for (int i = 0; i < first.size(); ++i) {
                Edge<CSCallSite, CSMethod> edge = first.get(i);
                Edge<CSCallSite, CSMethod> again = second.get(i);
                assertEquals(edge.hashCode(), again.hashCode());
                assertSame(edge.getClass(), again.getClass());
                if (!isLambdaEdge(edge)) {
                    continue;
                }
                ++lambdaEdges;
                assertNotSame(edge, again, "lambda edge retained: " + edge);
                assertTrue(((OtherEdge<?, ?>) again).propagatesExceptions());
                assertEquals(edge.hashCode(), ((SourcedEdge) edge).getSource()
                        .edgeHashCode(site, edge.getCallee()));
                assertTrue(site.getEdges().contains(edge));
                CSMethod callee = edge.getCallee();
                List<Edge<CSCallSite, CSMethod>> incoming = callee.getEdges();
                int at = incoming.indexOf(edge);
                assertTrue(at >= 0, "incoming edge of " + callee);
                Edge<CSCallSite, CSMethod> in = callee.getEdge(at);
                assertEquals(edge, in);
                assertEquals(edge.hashCode(), in.hashCode());
                assertSame(edge.getClass(), in.getClass());
                assertNotSame(in, callee.getEdge(at), "incoming lambda edge retained");
            }
        }
        assertTrue(lambdaEdges >= 6, "lambda edges: " + lambdaEdges);
    }

    /**
     * Equal sources of lambda edges are one object, so the call sites and
     * callees share them: one per non-capturing invokedynamic, one per
     * creating context of the capturing lambda.
     */
    @Test
    void lambdaEdgesShareTheirSources() {
        List<EdgeSource> sources = pta.getCSCallGraph().edges()
                .filter(LambdaEdgeStorageTest::isLambdaEdge)
                .map(edge -> ((SourcedEdge) edge).getSource())
                .toList();
        assertTrue(sources.size() >= 6, "lambda edges: " + sources.size());
        Map<EdgeSource, EdgeSource> first = Maps.newMap();
        for (EdgeSource source : sources) {
            assertSame(first.computeIfAbsent(source, s -> s), source,
                    "equal sources not shared: " + source);
        }
        assertTrue(first.size() < sources.size(),
                "sources " + first.size() + " of edges " + sources.size());
    }

    private static boolean isLambdaEdge(Edge<?, ?> edge) {
        return edge.getClass().getSimpleName().equals(LAMBDA_EDGE);
    }
}
