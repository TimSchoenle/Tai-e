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
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The option {@code lambda-heap-context}: {@code captured} gives a lambda
 * object without captured variables the empty heap context instead of the
 * context of the method that created it ({@code method}, the default). Under
 * context selectors of limit 1, which drop the heap context of a receiver,
 * the call graph and the points-to sets projected to objects stay equal as
 * long as no lambda object is the base of a field or an array access.
 */
public class LambdaHeapContextTest {

    private static final String PTA_ROOT = "src/test/resources/pta";

    private static final String LAMBDA_DESC = "LambdaObj";

    /**
     * The programs compared: the lambda test programs under each context
     * selector of limit 1, and the programs of {@link BasicTestFull},
     * {@link ContextSensitivityTest} and {@link ContextSensitivityTestFull}
     * with their options. The latter contain no lambda, so for them the
     * comparison only checks that the option changes nothing else.
     */
    static Stream<Arguments> programs() {
        List<Arguments> programs = new ArrayList<>();
        for (String main : List.of("Args", "LambdaConstructor", "LambdaInstanceMethod",
                "LambdaStaticMethod", "ImpreciseLambdas", "DispatchBugDueToLackOfSubclassCheck",
                "NativeModelWithLambda", "LambdaContexts", "LambdaSelfReceiver",
                "LambdaSharedReceiver", "LambdaSharedTargets", "Streams", "LambdaMix")) {
            for (String cs : List.of("cs:1-obj", "cs:1-call", "cs:1-type")) {
                programs.add(Arguments.of("lambda", main, cs));
            }
        }
        for (String main : List.of("StaticField", "Array", "Cast", "Cast2", "Null",
                "Primitive", "MultiArray", "Clinit", "ClassObj", "Native")) {
            programs.add(Arguments.of("basic", main, ""));
        }
        programs.add(Arguments.of("basic", "Primitives", "propagate-types:[reference,int,double];"
                + "plugins:[pascal.taie.analysis.pta.plugin.NumberLiteralHandler]"));
        programs.add(Arguments.of("basic", "PropagateNull", "propagate-types:[reference,null];"
                + "plugins:[pascal.taie.analysis.pta.plugin.NullHandler]"));
        programs.add(Arguments.of("basic", "Strings", ""));
        programs.add(Arguments.of("basic", "NativeModel", ""));
        programs.add(Arguments.of("basic", "Annotations", "cs:1-call"));
        programs.add(Arguments.of("basic", "ZeroLengthArray", "cs:1-obj-1h"));
        programs.add(Arguments.of("contextsensitivity", "OneCall", "cs:1-call;"
                + "propagate-types:[reference,int];"
                + "plugins:[pascal.taie.analysis.pta.plugin.NumberLiteralHandler]"));
        programs.add(Arguments.of("contextsensitivity", "OneObject", "cs:1-obj"));
        programs.add(Arguments.of("contextsensitivity", "OneType", "cs:1-type"));
        programs.add(Arguments.of("contextsensitivity", "TwoCall", "cs:2-call"));
        programs.add(Arguments.of("contextsensitivity", "TwoObject", "cs:2-obj"));
        programs.add(Arguments.of("contextsensitivity", "TwoType", "cs:2-type"));
        for (String[] program : List.of(
                new String[]{"RecursiveObj", "cs:2-obj"},
                new String[]{"LongObjContext", "cs:2-obj"},
                new String[]{"LongCallContext", "cs:2-call"},
                new String[]{"StaticSelect", "cs:2-obj"},
                new String[]{"TwoCallOnly", "cs:2-call"},
                new String[]{"ObjOnly", "cs:1-obj"},
                new String[]{"MustUseHeap", "cs:2-call"},
                new String[]{"NestedHeap", "cs:2-obj"},
                new String[]{"CallOnly", "cs:1-call"},
                new String[]{"LinkedQueue", "cs:2-obj"},
                new String[]{"TypeSens", "cs:2-type"},
                new String[]{"SpecialHeapContext", "cs:2-obj"})) {
            programs.add(Arguments.of("contextsensitivity", program[0], program[1]));
        }
        return programs.stream();
    }

    @ParameterizedTest(name = "{0}/{1} {2}")
    @MethodSource("programs")
    void capturedKeepsCallGraphAndObjectPointsToSets(String dir, String main, String opts) {
        Snapshot method = analyse(dir, main, opts, "method");
        Snapshot captured = analyse(dir, main, opts, "captured");
        assertEquals(method.csMethods(), captured.csMethods(), "CS methods");
        assertEquals(method.csEdges(), captured.csEdges(), "CS call edges");
        assertEquals(method.varPointsTo(), captured.varPointsTo(), "CS variables");
        assertEquals(method.heapPointsTo(), captured.heapPointsTo(), "fields and arrays");
        assertTrue(captured.lambdaObjs() <= method.lambdaObjs(),
                "lambda CS objects " + captured.lambdaObjs() + " > " + method.lambdaObjs());
        if (dir.equals("lambda")) {
            assertTrue(method.lambdaObjs() > 0, "no lambda CS object in " + main);
        }
    }

    /**
     * The three lambdas without captured variables of {@code LambdaContexts},
     * each created under three contexts, become one CS object each; the
     * capturing lambda keeps one per context.
     */
    @Test
    void captureFreeLambdaObjectsShareTheEmptyHeapContext() {
        assertEquals(12, analyse("lambda", "LambdaContexts", "cs:1-obj", "method").lambdaObjs());
        assertEquals(6, analyse("lambda", "LambdaContexts", "cs:1-obj", "captured").lambdaObjs());
    }

    /**
     * {@code LambdaMix} (compared above) creates capture-free lambdas under
     * several contexts of the creating method, so the comparison there runs
     * on fewer lambda CS objects with {@code captured}. Not under
     * {@code cs:1-type}: both receivers are allocated in the same class, so
     * the creating method has one context.
     */
    @ParameterizedTest
    @ValueSource(strings = {"cs:1-obj", "cs:1-call"})
    void capturedSharesLambdaObjectsOfLambdaMix(String cs) {
        long method = analyse("lambda", "LambdaMix", cs, "method").lambdaObjs();
        long captured = analyse("lambda", "LambdaMix", cs, "captured").lambdaObjs();
        assertTrue(captured < method, "lambda CS objects " + captured + " of " + method);
    }

    /**
     * The side condition: when a lambda object without captured variables
     * is the base of a field access, its field no longer differs per context
     * of the creating method, so a load under one context also sees the
     * value stored under the other. The points-to sets projected to
     * variables without contexts and to fields grouped by base object stay
     * equal; the one of the context-sensitive variable grows.
     */
    @Test
    void lambdaObjectAtFieldBaseMergesTheFieldOverContexts() {
        String opts = "cs:1-obj;plugins:[pascal.taie.analysis.pta.LambdaFieldBasePlugin]";
        Snapshot method = analyse("lambda", "LambdaFieldBase", opts, "method");
        Snapshot captured = analyse("lambda", "LambdaFieldBase", opts, "captured");
        assertEquals(method.csMethods(), captured.csMethods(), "CS methods");
        assertEquals(method.csEdges(), captured.csEdges(), "CS call edges");
        String loaded = "<FieldBaseSink: java.lang.Object load(java.lang.Object)>/loaded";
        Map<String, Set<String>> methodLoads = pointsToOf(method, loaded);
        Map<String, Set<String>> capturedLoads = pointsToOf(captured, loaded);
        assertEquals(2, methodLoads.size(), "contexts of " + loaded + ": " + methodLoads);
        methodLoads.values().forEach(objs -> assertEquals(1, objs.size(), loaded + ": " + objs));
        assertEquals(methodLoads.keySet(), capturedLoads.keySet(), "contexts of " + loaded);
        capturedLoads.values().forEach(objs -> assertEquals(2, objs.size(), loaded + ": " + objs));
        assertEquals(union(methodLoads), union(capturedLoads), "context-insensitive " + loaded);
        assertEquals(method.heapPointsTo(), captured.heapPointsTo(),
                "fields and arrays grouped by base object");
    }

    /**
     * Beyond limit 1: a context selector of limit 2 puts the heap context of
     * the receiver into the callee context, so a default method called on a
     * capture-free lambda object created under two contexts has two CS
     * methods with {@code method} and one with {@code captured}.
     */
    @Test
    void limitTwoMergesCalleeContextsOfLambdaReceivers() {
        String describe = "<Described: java.lang.Object describe()>";
        assertEquals(2, contextsOf(
                analyse("lambda", "LambdaDefaultMethod", "cs:2-obj", "method"), describe));
        assertEquals(1, contextsOf(
                analyse("lambda", "LambdaDefaultMethod", "cs:2-obj", "captured"), describe));
    }

    @Test
    void rejectsAnUnknownOption() {
        Throwable thrown = assertThrows(RuntimeException.class,
                () -> analyse("lambda", "LambdaContexts", "cs:1-obj", "creator"));
        while (thrown.getCause() != null && !(thrown instanceof IllegalArgumentException)) {
            thrown = thrown.getCause();
        }
        assertEquals("Illegal lambda-heap-context option: creator", thrown.getMessage());
    }

    /**
     * The facts compared between the two options, with every context and
     * object written as text: CS methods, CS call edges, the points-to set
     * of each CS variable and the points-to sets of the fields, array
     * elements and static fields grouped by their base object without heap
     * context, all projected to objects; and the number of lambda CS
     * objects.
     */
    private record Snapshot(Set<String> csMethods, Set<String> csEdges,
                            Map<String, Set<String>> varPointsTo,
                            Map<String, Set<String>> heapPointsTo, long lambdaObjs) {
    }

    private static Snapshot analyse(String dir, String main, String opts, String heapContext) {
        String ptaOpts = "implicit-entries:false;only-app:true;distinguish-string-constants:all;"
                + "handle-invokedynamic:true;lambda-heap-context:" + heapContext
                + (opts.isEmpty() ? "" : ";" + opts);
        Main.main("-cp", PTA_ROOT, "-cp", PTA_ROOT + "/" + dir, "-m", main,
                "-a", "pta=" + ptaOpts);
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        Set<String> csMethods = pta.getCSCallGraph().reachableMethods()
                .map(m -> m.getContext() + " " + m.getMethod().getSignature())
                .collect(Collectors.toCollection(Sets::newOrderedSet));
        Set<String> csEdges = pta.getCSCallGraph().edges()
                .map(LambdaHeapContextTest::edgeText)
                .collect(Collectors.toCollection(Sets::newOrderedSet));
        Map<String, Set<String>> varPointsTo = Maps.newOrderedMap();
        for (CSVar csVar : pta.getCSVars()) {
            Var var = csVar.getVar();
            varPointsTo.put(csVar.getContext() + "\t" + var.getMethod().getSignature()
                    + "/" + var.getName(), objects(csVar));
        }
        Map<String, Set<String>> heapPointsTo = Maps.newOrderedMap();
        pta.getInstanceFields().forEach(f -> heapPointsTo.computeIfAbsent(
                f.getBase().getObject() + "." + f.getField().getSignature(),
                k -> Sets.newOrderedSet()).addAll(objects(f)));
        pta.getArrayIndexes().forEach(a -> heapPointsTo.computeIfAbsent(
                a.getArray().getObject() + "[*]", k -> Sets.newOrderedSet()).addAll(objects(a)));
        pta.getStaticFields().forEach(f -> heapPointsTo.computeIfAbsent(
                f.getField().getSignature(), k -> Sets.newOrderedSet()).addAll(objects(f)));
        long lambdaObjs = pta.getCSObjects().stream()
                .map(CSObj::getObject)
                .filter(o -> o instanceof MockObj mock
                        && mock.getDescriptor().string().equals(LAMBDA_DESC))
                .count();
        return new Snapshot(csMethods, csEdges, varPointsTo, heapPointsTo, lambdaObjs);
    }

    private static String edgeText(Edge<CSCallSite, CSMethod> edge) {
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod callee = edge.getCallee().getMethod();
        return edge.getCallSite().getContext() + " " + callSite.getContainer().getSignature()
                + "@" + callSite.getIndex() + " " + edge.getKind() + " "
                + edge.getCallee().getContext() + " " + callee.getSignature();
    }

    private static Set<String> objects(Pointer pointer) {
        return pointer.getObjects().stream()
                .map(o -> o.getObject().toString())
                .collect(Collectors.toCollection(Sets::newOrderedSet));
    }

    /**
     * @return the points-to sets of the variable {@code methodAndVar} (the
     * method signature, a slash and the variable name) keyed by context.
     */
    private static Map<String, Set<String>> pointsToOf(Snapshot snapshot, String methodAndVar) {
        Map<String, Set<String>> byContext = Maps.newOrderedMap();
        snapshot.varPointsTo().forEach((key, objs) -> {
            int tab = key.indexOf('\t');
            if (key.substring(tab + 1).equals(methodAndVar)) {
                byContext.put(key.substring(0, tab), objs);
            }
        });
        return byContext;
    }

    private static long contextsOf(Snapshot snapshot, String methodSig) {
        return snapshot.csMethods().stream()
                .filter(m -> m.endsWith(" " + methodSig))
                .count();
    }

    private static Set<String> union(Map<String, Set<String>> byContext) {
        Set<String> all = Sets.newOrderedSet();
        byContext.values().forEach(all::addAll);
        return all;
    }
}
