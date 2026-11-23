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
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The context-sensitive lambda call edges of method references without
 * captured variables (instance, static, constructor) and of a capturing
 * lambda, each created under three contexts (cs:1-obj) and called at one
 * site.
 */
public class LambdaEdgeContextTest {

    private static PointerAnalysisResult pta;

    private static ClassHierarchy hierarchy;

    @BeforeAll
    static void analyse() {
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", "LambdaContexts",
                "-a", "pta=cs:1-obj;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true");
        pta = World.get().getResult(PointerAnalysis.ID);
        hierarchy = World.get().getClassHierarchy();
    }

    /**
     * A lambda without captured variables reads nothing under the context of
     * the method that created it, so the call site and each callee context
     * of {@code Item::name} share one edge, whichever of the three lambda
     * objects reached the site.
     */
    @Test
    void instanceReferenceHasOneEdgePerCalleeContext() {
        assertOneEdgePerCallee(
                "<LambdaContexts: java.lang.Object apply(java.util.function.Function,Item)>",
                "<Item: java.lang.Object name()>", 3);
    }

    /** The same for the static method reference {@code Item::id}. */
    @Test
    void staticReferenceHasOneEdgePerCalleeContext() {
        assertOneEdgePerCallee(
                "<LambdaContexts: java.lang.Object applyStatic(java.util.function.Function,Item)>",
                "<Item: java.lang.Object id(Item)>", 1);
    }

    /**
     * The same for the constructor reference {@code Item::new}, whose
     * created object still reaches the result of the call site.
     */
    @Test
    void constructorReferenceHasOneEdgePerCalleeContext() {
        String create = "<LambdaContexts: Item create(java.util.function.Supplier)>";
        assertOneEdgePerCallee(create, "<Item: void <init>()>", 1);
        JMethod caller = hierarchy.getMethod(create);
        assertEquals(1, pta.getPointsToSet(caller.getIR().getReturnVars().get(0)).size(),
                "objects created through Item::new");
    }

    /**
     * A capturing lambda keeps one edge per creating context, so the value
     * captured under each of them reaches the body.
     */
    @Test
    void capturingLambdaKeepsTheCapturedValueOfEveryContext() {
        JClass maker = hierarchy.getClass("Maker");
        List<JMethod> bodies = maker.getDeclaredMethods().stream()
                .filter(m -> m.getName().startsWith("lambda$prefix$"))
                .toList();
        assertEquals(1, bodies.size(), "lambda bodies of Maker.prefix");
        JMethod body = bodies.get(0);
        JMethod capture = hierarchy.getMethod(
                "<LambdaContexts: java.lang.Object capture(java.util.function.Function,Item)>");
        assertEquals(3, edges(capture, body).size(), "edges into " + body);
        assertEquals(3, pta.getPointsToSet(body.getIR().getParam(0)).size(),
                "captured tags reaching " + body);
    }

    private static void assertOneEdgePerCallee(
            String callerSig, String calleeSig, int calleeContexts) {
        JMethod callee = hierarchy.getMethod(calleeSig);
        List<Edge<CSCallSite, CSMethod>> edges = edges(hierarchy.getMethod(callerSig), callee);
        Set<CSMethod> callees = edges.stream()
                .map(Edge::getCallee)
                .collect(Collectors.toSet());
        assertEquals(calleeContexts, callees.size(), "callee contexts of " + callee);
        assertEquals(callees.size(), edges.size(), "edges into " + callee);
    }

    private static List<Edge<CSCallSite, CSMethod>> edges(JMethod caller, JMethod callee) {
        return pta.getCSCallGraph().edges()
                .filter(edge -> edge.getCallSite().getCallSite().getContainer().equals(caller)
                        && edge.getCallee().getMethod().equals(callee))
                .toList();
    }
}
