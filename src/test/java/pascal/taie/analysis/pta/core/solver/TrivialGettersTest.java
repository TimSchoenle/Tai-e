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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.ConfigException;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code trivial-getters} (px/s115-P57): a run with the option off
 * and a run with it on give the same call edges, the same reachable methods
 * and the same points-to sets of every variable outside the trivial getters
 * where the callee context fixes the receiver object (1-obj, 2-obj), and
 * subsets of them elsewhere (a call merges the receivers of one callee
 * context, the load at the call site does not). The variables of a trivial
 * getter taken as a load hold nothing: that is the option's contract, so the
 * option is refused where they are read (Zipper, Scaler, Mahjong, taint).
 */
public class TrivialGettersTest {

    private static final String DIR = "getters";

    private static final String MAIN = "Getters";

    private static final String ON = "trivial-getters:true";

    private static final String OFF = "trivial-getters:false";

    /** The trivial getters of the fixture. */
    private static final Map<String, TrivialGetter.Form> TRIVIAL = Map.of(
            "<Box: java.lang.Object get()>", TrivialGetter.Form.INSTANCE_FIELD,
            "<Base: java.lang.Object val()>", TrivialGetter.Form.INSTANCE_FIELD,
            "<Sub1: java.lang.Object val()>", TrivialGetter.Form.INSTANCE_FIELD,
            "<Box: java.lang.Object viaStatic()>", TrivialGetter.Form.STATIC_FIELD,
            "<Holder: java.lang.Object sget()>", TrivialGetter.Form.STATIC_FIELD,
            "<Box: java.lang.Object nothing()>", TrivialGetter.Form.NULL,
            "<Holder: java.lang.Object none()>", TrivialGetter.Form.NULL);

    /** Instance methods of the fixture that look like getters but are not trivial. */
    private static final Set<String> NOT_TRIVIAL = Set.of(
            "<Box: GtA getA()>", "<Box: java.lang.Object pick(Box)>",
            "<Box: int size()>", "<Sub2: java.lang.Object val()>");

    @Test
    void shapes() {
        Tests.testPTA(false, DIR, MAIN, OFF);
        TRIVIAL.forEach((sig, form) ->
                assertEquals(form, TrivialGetter.of(method(sig)).form(),
                        () -> sig + " " + method(sig).getIR().getStmts()));
        NOT_TRIVIAL.forEach(sig ->
                assertEquals(TrivialGetter.Form.NONE, TrivialGetter.of(method(sig)).form(), sig));
    }

    @ParameterizedTest
    @ValueSource(strings = {"advanced:zipper",
            "taint-config:src/test/resources/pta/taint/taint-config-call-source.yml"})
    void refusedWhereTheGettersThisVariableIsRead(String option) {
        Throwable thrown = assertThrows(Throwable.class,
                () -> Tests.testPTA(false, DIR, MAIN, ON, option));
        assertTrue(Stream.iterate(thrown, t -> t != null, Throwable::getCause)
                        .anyMatch(t -> t instanceof ConfigException
                                && t.getMessage().startsWith("trivial-getters is refused")),
                thrown::toString);
    }

    @ParameterizedTest
    @ValueSource(strings = {"1-obj", "2-obj"})
    void sameResultWhereTheCalleeContextFixesTheReceiver(String cs) {
        Snapshot off = run(cs, OFF);
        Snapshot on = run(cs, ON);
        assertEquals(off.edges(), on.edges(), cs + ": call edges");
        assertEquals(off.reached(), on.reached(), cs + ": reachable methods");
        assertEquals(off.pointsTo(), on.pointsTo(), cs + ": points-to sets outside the getters");
        assertTakenAsLoads(off, on);
    }

    @ParameterizedTest
    @ValueSource(strings = {"ci", "1-call", "2-type"})
    void subsetWhereACalleeContextMergesReceivers(String cs) {
        Snapshot off = run(cs, OFF);
        Snapshot on = run(cs, ON);
        assertTrue(off.edges().containsAll(on.edges()), cs + ": call edges");
        assertTrue(off.reached().containsAll(on.reached()), cs + ": reachable methods");
        assertEquals(off.pointsTo().keySet(), on.pointsTo().keySet(), cs + ": variables");
        off.pointsTo().forEach((var, objs) ->
                assertTrue(objs.containsAll(on.pointsTo().get(var)), cs + ": " + var));
        // every call edge into a trivial getter is kept
        off.edges().stream()
                .filter(e -> TRIVIAL.keySet().stream().anyMatch(e::endsWith))
                .forEach(e -> assertTrue(on.edges().contains(e), cs + ": " + e));
        // the fixture's own calls are all still there
        assertTrue(on.edges().stream().anyMatch(e -> e.endsWith("<GtD: void run()>")), cs);
        assertTakenAsLoads(off, on);
    }

    /**
     * The trivial getters' this variables are empty with the option on and
     * not with it off; the other getters' are never empty.
     */
    private static void assertTakenAsLoads(Snapshot off, Snapshot on) {
        TRIVIAL.forEach((sig, form) -> {
            if (form == TrivialGetter.Form.INSTANCE_FIELD) {
                assertFalse(off.thisPointsTo().get(sig).isEmpty(), "off: " + sig);
                assertTrue(on.thisPointsTo().get(sig).isEmpty(), "on: " + sig);
            }
        });
        NOT_TRIVIAL.forEach(sig ->
                assertFalse(on.thisPointsTo().get(sig).isEmpty(), "on: " + sig));
    }

    private static JMethod method(String signature) {
        return Objects.requireNonNull(World.get().getClassHierarchy().getMethod(signature),
                signature);
    }

    private record Snapshot(Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo,
                            Map<String, Set<String>> thisPointsTo) {
    }

    private static Snapshot run(String cs, String option) {
        Tests.testPTA(false, DIR, MAIN, "cs:" + cs, option);
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
            if (!TRIVIAL.containsKey(var.getMethod().getSignature())) {
                pointsTo.put(var.getMethod() + "/" + var.getName(), texts(pta.getPointsToSet(var)));
            }
        }
        Map<String, Set<String>> thisPointsTo = new TreeMap<>();
        for (String sig : TRIVIAL.keySet()) {
            thisPointsTo.put(sig, thisPointsTo(pta, sig));
        }
        for (String sig : NOT_TRIVIAL) {
            thisPointsTo.put(sig, thisPointsTo(pta, sig));
        }
        return new Snapshot(edges, reached, pointsTo, thisPointsTo);
    }

    private static Set<String> thisPointsTo(PointerAnalysisResult pta, String sig) {
        JMethod method = method(sig);
        return method.isStatic() ? Set.of() : texts(pta.getPointsToSet(method.getIR().getThis()));
    }

    private static Set<String> texts(Set<Obj> objs) {
        return objs.stream().map(Obj::toString).collect(Collectors.toCollection(TreeSet::new));
    }
}
