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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.invokedynamic.LambdaAnalysis;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A lambda object of {@code altMetafactory} is typed by a class that
 * implements the interfaces the flags add, so it passes every type filter of
 * them and dispatches their default methods, while an interface the flags do
 * not add still filters it (fixture {@code LambdaAddedInterfaces}).
 */
public class LambdaAddedInterfacesTest {

    private static final String MAIN = "LambdaAddedInterfaces";

    private static final List<String> REACHED = List.of(
            "castBody", "storeBody", "parameterBody", "reflectiveBody",
            "markBody", "actBody");

    private static final List<String> UNREACHED = List.of(
            "negCastBody", "negStoreBody", "negPlainBody", "negBaseBody");

    private static PointerAnalysisResult analyse(String cs) {
        long start = System.nanoTime();
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", MAIN,
                "-a", "pta=cs:" + cs + ";handle-invokedynamic:true;");
        PointerAnalysisResult result = World.get().getResult(PointerAnalysis.ID);
        CallGraph<Invoke, JMethod> callGraph = result.getCallGraph();
        System.out.println("[lf] cs=" + cs
                + " reached=" + callGraph.getNumberOfMethods()
                + " edges=" + callGraph.getNumberOfEdges()
                + " objects=" + result.getObjects().size()
                + " ms=" + (System.nanoTime() - start) / 1_000_000);
        return result;
    }

    private static Set<String> reachedNames(PointerAnalysisResult result) {
        return result.getCallGraph().reachableMethods()
                .filter(m -> m.getDeclaringClass().getName().equals(MAIN))
                .map(JMethod::getName)
                .collect(Collectors.toSet());
    }

    @Test
    void addedInterfacesPassFiltersAndOthersDoNot() {
        for (String cs : List.of("ci", "1-obj")) {
            Set<String> reached = reachedNames(analyse(cs));
            for (String name : REACHED) {
                assertTrue(reached.contains(name), cs + ": " + name + " unreached");
            }
            for (String name : UNREACHED) {
                assertFalse(reached.contains(name), cs + ": " + name + " reached");
            }
        }
    }

    @Test
    void lambdaObjectsAreTypedByTheirInterfaces() {
        PointerAnalysisResult result = analyse("ci");
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JClass marker = hierarchy.getClass(MAIN + "$Marker");
        JClass other = hierarchy.getClass(MAIN + "$Other");
        JClass runnable = hierarchy.getClass("java.lang.Runnable");
        JClass serializable = hierarchy.getClass("java.io.Serializable");
        assertNotNull(marker);
        assertNotNull(other);
        assertNotNull(runnable);
        assertNotNull(serializable);
        // the lambda objects the fixture creates (the library creates more)
        List<Obj> lambdas = result.getObjects().stream()
                .filter(LambdaAnalysis::isLambdaObj)
                .filter(o -> o.getContainerMethod()
                        .map(m -> m.getDeclaringClass().getName().equals(MAIN))
                        .orElse(false))
                .toList();
        // per method of the fixture: Runnable & Serializable (cast, array
        // store, lambda parameter, reflective argument, negOtherArrayStore),
        // Runnable & Marker (markerDefault, negOtherCast), Act &
        // Serializable, the plain Runnable and the Consumer of
        // lambdaParameter
        long markerLambdas = lambdas.stream()
                .filter(o -> hierarchy.isSubclass(marker, jclassOf(o)))
                .count();
        long serializableLambdas = lambdas.stream()
                .filter(o -> hierarchy.isSubclass(serializable, jclassOf(o)))
                .count();
        assertEquals(2, markerLambdas);
        assertEquals(6, serializableLambdas);
        assertTrue(lambdas.stream().noneMatch(o -> hierarchy.isSubclass(other, jclassOf(o))));
        // the plain lambda keeps its functional interface
        assertEquals(1, lambdas.stream().filter(o -> jclassOf(o) == runnable).count());
        // the classes of the marker lambdas dispatch the marker's default
        // method and no method they declare, the run method of the lambda
        JMethod mark = hierarchy.getMethod("<" + MAIN + "$Marker: void mark()>");
        JMethod run = hierarchy.getMethod("<java.lang.Runnable: void run()>");
        assertNotNull(mark);
        assertNotNull(run);
        lambdas.stream().filter(o -> hierarchy.isSubclass(marker, jclassOf(o))).forEach(o -> {
            JClass c = jclassOf(o);
            assertTrue(c.isFinal());
            assertEquals(mark, hierarchy.dispatch(c, mark.getRef()));
            assertNull(hierarchy.dispatch(c, run.getRef()));
        });
    }

    private static JClass jclassOf(Obj o) {
        return ((ClassType) o.getType()).getJClass();
    }
}
