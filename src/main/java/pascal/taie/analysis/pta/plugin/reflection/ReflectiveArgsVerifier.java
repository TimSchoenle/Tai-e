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

package pascal.taie.analysis.pta.plugin.reflection;

import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MockPointer;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * Checks the relay pointers of {@link ReflectiveActionModel} against the
 * edges they replace: one parameter-passing edge, filtered by the parameter
 * type, from the elements of every array the argument variable points to
 * into every reference parameter of every reflective callee.
 * <p>
 * At the end of the analysis the relay must pass to every callee parameter
 * exactly the objects those edges would pass, hold exactly the elements of
 * those arrays, and every parameter must contain what the edges would pass
 * (an analysis stopped by its time limit ends with work left, so this check
 * does not apply to it). At each phase end and while the solver runs
 * (every {@code px.reflargs.verify.every} seconds, default 60), pending
 * propagation may still be on the worklist, so only the absence of any
 * extra object is checked. Enabled by {@code -Dpx.reflargs.verify=true};
 * a difference throws {@link IllegalStateException}.
 */
final class ReflectiveArgsVerifier {

    private static final String ENABLED = "px.reflargs.verify";

    private static final String EVERY = "px.reflargs.verify.every";

    private final CSManager csManager;

    private final TypeSystem typeSystem;

    private final Map<CSVar, MockPointer> relays;

    private final MultiMap<CSVar, ReflectiveCallEdge> edges = Maps.newMultiMap();

    private final long intervalNanos;

    private long nextCheck;

    ReflectiveArgsVerifier(Solver solver, Map<CSVar, MockPointer> relays) {
        this.csManager = solver.getCSManager();
        this.typeSystem = solver.getTypeSystem();
        this.relays = relays;
        this.intervalNanos = TimeUnit.SECONDS.toNanos(Long.getLong(EVERY, 60L));
        this.nextCheck = System.nanoTime() + intervalNanos;
    }

    static boolean isEnabled() {
        return Boolean.getBoolean(ENABLED);
    }

    void addEdge(CSVar csArgs, ReflectiveCallEdge edge) {
        edges.put(csArgs, edge);
    }

    /**
     * Runs the running-solver check when its interval has passed.
     */
    void onProgress() {
        if (System.nanoTime() - nextCheck >= 0) {
            verify(false);
            nextCheck = System.nanoTime() + intervalNanos;
        }
    }

    /**
     * @param quiescent whether the analysis has finished
     */
    void verify(boolean quiescent) {
        long originalEdges = 0;
        long relayEdges = 0;
        long params = 0;
        for (Map.Entry<CSVar, MockPointer> entry : relays.entrySet()) {
            CSVar csArgs = entry.getKey();
            MockPointer relay = entry.getValue();
            Set<CSObj> arrays = csArgs.getObjects();
            Set<CSObj> elements = new HashSet<>();
            arrays.forEach(array ->
                    elements.addAll(csManager.getArrayIndex(array).getObjects()));
            Set<CSObj> relayed = relay.getObjects();
            if (quiescent ? !relayed.equals(elements) : !elements.containsAll(relayed)) {
                fail(relay, "holds " + relayed.size() + " objects, the argument arrays "
                        + elements.size());
            }
            Map<Pointer, Type> expected = expectedParams(csArgs);
            Set<Pointer> targets = new HashSet<>();
            for (PointerFlowEdge out : relay.getOutEdges()) {
                Pointer param = out.target();
                targets.add(param);
                Type type = expected.get(param);
                if (type == null) {
                    fail(relay, "passes to " + param + ", which no reflective callee declares");
                }
                checkParam(relay, out, type, elements, quiescent);
            }
            if (!targets.equals(expected.keySet())) {
                fail(relay, "passes to " + targets.size() + " parameters, expected "
                        + expected.size());
            }
            originalEdges += (long) arrays.size() * expected.size();
            relayEdges += arrays.size() + targets.size();
            params += expected.size();
        }
        System.err.printf("[refl] reflective args verified (%s): relays=%d params=%d"
                        + " relay_edges=%d replaced_edges=%d%n",
                quiescent ? "finish" : "running", relays.size(), params,
                relayEdges, originalEdges);
    }

    /**
     * The reference parameters of every reflective callee of the calls that
     * use the argument variable, with their declared types.
     */
    private Map<Pointer, Type> expectedParams(CSVar csArgs) {
        Map<Pointer, Type> expected = new HashMap<>();
        for (ReflectiveCallEdge edge : edges.get(csArgs)) {
            JMethod callee = edge.getCallee().getMethod();
            callee.getIR().getParams().forEach(param -> {
                if (ReflectiveActionModel.isConcerned(param.getType())) {
                    expected.put(csManager.getCSVar(edge.getCallee().getContext(), param),
                            param.getType());
                }
            });
        }
        return expected;
    }

    private void checkParam(MockPointer relay, PointerFlowEdge out, Type type,
                            Set<CSObj> elements, boolean quiescent) {
        Set<CSObj> original = new HashSet<>();
        for (CSObj obj : elements) {
            if (typeSystem.isSubtype(type, obj.getObject().getType())) {
                original.add(obj);
            }
        }
        Set<CSObj> passed = new HashSet<>();
        PointsToSet relayed = relay.getPointsToSet();
        if (relayed != null) {
            out.forEachTransfer(transfer ->
                    passed.addAll(transfer.apply(out, relayed).getObjects()));
        }
        Pointer param = out.target();
        if (quiescent ? !passed.equals(original) : !original.containsAll(passed)) {
            fail(relay, "passes " + passed.size() + " objects to " + param
                    + ", the replaced edges " + original.size());
        }
        if (quiescent) {
            // a filter of the parameter pointer drops an object on either path
            Set<CSObj> held = param.getObjects();
            for (CSObj obj : original) {
                if (!held.contains(obj)
                        && param.getFilters().stream().allMatch(f -> f.test(obj))) {
                    fail(relay, "left " + obj + " out of " + param);
                }
            }
        }
    }

    private static void fail(MockPointer relay, String what) {
        throw new IllegalStateException("[refl] relay " + relay + " " + what);
    }
}
