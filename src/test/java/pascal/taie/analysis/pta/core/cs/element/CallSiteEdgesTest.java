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

package pascal.taie.analysis.pta.core.cs.element;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.callgraph.OtherEdge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.OpenHashSet;

import java.util.ArrayList;
import java.util.ConcurrentModificationException;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Call edges of call sites and CS methods: a plain edge is held without its
 * object, and every reader sees the edges, their order and their hash
 * codes as an {@link OpenHashSet} and an insertion-ordered list of the
 * added edge objects give them.
 */
public class CallSiteEdgesTest {

    private final Context context = new TrieContext.Factory<>().getEmptyContext();

    private final CSMethod caller = new CSMethod(null, context);

    @Test
    void plainEdgeIsRebuiltNotRetained() {
        CSCallSite site = staticSite();
        CSMethod callee = new CSMethod(null, context);
        Edge<CSCallSite, CSMethod> edge = new Edge<>(CallKind.STATIC, site, callee);
        assertTrue(site.addEdge(edge));
        callee.addEdge(edge);

        Edge<CSCallSite, CSMethod> out = site.getEdges().iterator().next();
        assertNotSame(edge, out);
        assertEquals(edge, out);
        assertEquals(edge.hashCode(), out.hashCode());
        assertSame(Edge.class, out.getClass());

        Edge<CSCallSite, CSMethod> in = callee.getEdge(0);
        assertNotSame(edge, in);
        assertEquals(edge, in);
        assertSame(site, in.getCallSite());
        assertSame(callee, in.getCallee());
        assertFalse(site.addEdge(new Edge<>(CallKind.STATIC, site, callee)));
    }

    /**
     * The allocation-free lookup agrees with {@code contains} of a new plain
     * edge while the set is a single element, dense and a hash table.
     */
    @Test
    void hasPlainEdgeAgreesWithContainsInEveryLayout() {
        CSCallSite site = staticSite();
        List<CSMethod> callees = new ArrayList<>();
        for (int i = 0; i < 4 * OpenHashSet.SMALL_LIMIT; i++) {
            callees.add(new CSMethod(null, context));
        }
        for (int added = 0; added < callees.size(); added++) {
            for (int i = 0; i < callees.size(); i++) {
                CSMethod callee = callees.get(i);
                boolean expected = site.getEdges().contains(
                        new Edge<>(CallKind.STATIC, site, callee));
                assertEquals(i < added, expected);
                assertEquals(expected, site.hasPlainEdge(CallKind.STATIC, callee));
            }
            site.addEdge(new Edge<>(CallKind.STATIC, site, callees.get(added)));
        }
        assertTrue(site.hasPlainEdge(CallKind.STATIC, callees.get(0)));
        // another kind is not this site's plain kind: unknown, so false
        assertFalse(site.hasPlainEdge(CallKind.VIRTUAL, callees.get(0)));
    }

    @Test
    void hasPlainEdgeIgnoresEdgesThatAreNotPlain() {
        CSCallSite site = staticSite();
        CSMethod callee = new CSMethod(null, context);
        site.addEdge(new Edge<>(CallKind.OTHER, site, callee));
        site.addEdge(new TestOtherEdge(site, callee));
        site.addEdge(new Edge<>(CallKind.STATIC, staticSite(), callee));
        assertFalse(site.hasPlainEdge(CallKind.STATIC, callee));
        assertFalse(site.hasPlainEdge(CallKind.OTHER, callee));
        CSCallSite unknownKind = new CSCallSite(null, context, caller);
        unknownKind.addEdge(new Edge<>(CallKind.STATIC, unknownKind, callee));
        assertFalse(unknownKind.hasPlainEdge(CallKind.STATIC, callee));
    }

    @Test
    void otherEdgesAreHeldAsAdded() {
        CSCallSite site = staticSite();
        CSMethod callee = new CSMethod(null, context);
        Edge<CSCallSite, CSMethod> otherKind = new Edge<>(CallKind.OTHER, site, callee);
        Edge<CSCallSite, CSMethod> subclass = new TestOtherEdge(site, callee);
        Edge<CSCallSite, CSMethod> plain = new Edge<>(CallKind.STATIC, site, callee);
        assertTrue(site.addEdge(otherKind));
        assertTrue(site.addEdge(subclass));
        assertTrue(site.addEdge(plain));
        callee.addEdge(otherKind);
        callee.addEdge(subclass);
        callee.addEdge(plain);

        List<Edge<CSCallSite, CSMethod>> out = List.copyOf(site.getEdges());
        assertSame(otherKind, out.get(0));
        assertSame(subclass, out.get(1));
        assertNotSame(plain, out.get(2));
        assertEquals(List.of(otherKind, subclass, plain), out);
        assertSame(otherKind, callee.getEdge(0));
        assertSame(subclass, callee.getEdge(1));
        assertEquals(List.of(otherKind, subclass, plain), callee.getEdges());
    }

    @Test
    void edgeFromAnotherSiteOrToAnotherCalleeIsHeldAsAdded() {
        CSCallSite site = staticSite();
        CSCallSite elsewhere = staticSite();
        CSMethod callee = new CSMethod(null, context);
        CSMethod target = new CSMethod(null, context);
        Edge<CSCallSite, CSMethod> foreign = new Edge<>(CallKind.STATIC, elsewhere, callee);
        assertTrue(site.addEdge(foreign));
        assertSame(foreign, site.getEdges().iterator().next());
        target.addEdge(new Edge<>(CallKind.STATIC, site, callee));
        assertSame(callee, target.getEdge(0).getCallee());
    }

    @Test
    void incomingEdgesFailFastOnAnEdgeAddedWhileReading() {
        CSMethod callee = new CSMethod(null, context);
        callee.addEdge(new Edge<>(CallKind.STATIC, staticSite(), callee));
        callee.addEdge(new Edge<>(CallKind.STATIC, staticSite(), callee));
        Runnable addOne = () -> callee.addEdge(
                new Edge<>(CallKind.STATIC, staticSite(), callee));
        List<Edge<CSCallSite, CSMethod>> view = callee.getEdges();
        assertThrows(ConcurrentModificationException.class,
                () -> view.forEach(e -> addOne.run()));
        assertThrows(ConcurrentModificationException.class, () -> {
            for (Edge<CSCallSite, CSMethod> ignored : view) {
                addOne.run();
            }
        });
        assertThrows(ConcurrentModificationException.class,
                () -> view.stream().forEach(e -> addOne.run()));
    }

    @Test
    void readersSeeTheEdgesInTheOrderOfTheObjectStore() {
        for (long seed = 1; seed <= 12; ++seed) {
            checkAgainstObjectStore(new Random(seed), 2 + (int) seed * 25);
        }
    }

    /**
     * Adds a random stream of plain, other-kind, subclass and duplicate
     * edges to call sites and their callees, and compares every reader with
     * an {@link OpenHashSet} per call site and a list per callee that hold
     * the added edge objects.
     */
    private void checkAgainstObjectStore(Random random, int calleeCount) {
        List<CSCallSite> sites = List.of(staticSite(), virtualSite(), staticSite(),
                new CSCallSite(null, context, caller));
        List<CSMethod> callees = new ArrayList<>();
        for (int i = 0; i < calleeCount; ++i) {
            callees.add(new CSMethod(null, context));
        }
        Map<CSCallSite, Set<Edge<CSCallSite, CSMethod>>> outRef = Maps.newMap();
        Map<CSMethod, List<Edge<CSCallSite, CSMethod>>> inRef = Maps.newMap();
        List<Edge<CSCallSite, CSMethod>> probes = new ArrayList<>();
        for (int step = 0; step < calleeCount * 6; ++step) {
            CSCallSite site = sites.get(random.nextInt(sites.size()));
            CSMethod callee = callees.get(random.nextInt(callees.size()));
            Edge<CSCallSite, CSMethod> edge = randomEdge(random, site, callee);
            probes.add(edge);
            boolean expected = outRef.computeIfAbsent(site, s -> new OpenHashSet<>()).add(edge);
            assertEquals(expected, site.addEdge(edge));
            if (expected) {
                callee.addEdge(edge);
                inRef.computeIfAbsent(callee, c -> new ArrayList<>()).add(edge);
            }
            Set<Edge<CSCallSite, CSMethod>> siteRef = outRef.get(site);
            if (siteRef.size() <= OpenHashSet.SMALL_LIMIT * 3) {
                // dense phase, the rehash and the first growth
                assertEquals(List.copyOf(siteRef), List.copyOf(site.getEdges()));
                assertEquals(hashes(siteRef), hashes(site.getEdges()));
                for (Edge<CSCallSite, CSMethod> probe : probes) {
                    assertEquals(siteRef.contains(probe), site.getEdges().contains(probe));
                }
            }
        }
        for (CSCallSite site : sites) {
            Set<Edge<CSCallSite, CSMethod>> expected = outRef.getOrDefault(site, Set.of());
            Set<Edge<CSCallSite, CSMethod>> actual = site.getEdges();
            assertEquals(expected.size(), actual.size());
            assertEquals(List.copyOf(expected), List.copyOf(actual));
            assertEquals(hashes(expected), hashes(actual));
            for (Edge<CSCallSite, CSMethod> probe : probes) {
                assertEquals(expected.contains(probe), actual.contains(probe));
            }
        }
        for (CSMethod callee : callees) {
            List<Edge<CSCallSite, CSMethod>> expected = inRef.getOrDefault(callee, List.of());
            assertEquals(expected, callee.getEdges());
            assertEquals(expected.size(), callee.getEdgeCount());
            for (int i = 0; i < expected.size(); ++i) {
                assertEquals(expected.get(i), callee.getEdge(i));
                assertSame(expected.get(i).getClass(), callee.getEdge(i).getClass());
            }
        }
    }

    private Edge<CSCallSite, CSMethod> randomEdge(
            Random random, CSCallSite site, CSMethod callee) {
        int pick = random.nextInt(10);
        if (pick == 0) {
            return new Edge<>(CallKind.OTHER, site, callee);
        } else if (pick == 1) {
            return new TestOtherEdge(site, callee);
        } else if (pick == 2) {
            return new Edge<>(CallKind.VIRTUAL, site, callee);
        }
        CallKind kind = site.getCallSite() == null
                ? CallKind.STATIC
                : CallGraphs.getCallKind(site.getCallSite());
        return new Edge<>(kind, site, callee);
    }

    private static List<Integer> hashes(Set<Edge<CSCallSite, CSMethod>> edges) {
        List<Integer> result = new ArrayList<>();
        edges.forEach(e -> result.add(e.hashCode()));
        return result;
    }

    private CSCallSite staticSite() {
        return new CSCallSite(new Invoke(null, new InvokeStatic(null, List.of())),
                context, caller);
    }

    private CSCallSite virtualSite() {
        Var base = new Var(null, "base", null, 0);
        return new CSCallSite(new Invoke(null, new InvokeVirtual(null, base, List.of())),
                context, caller);
    }

    private static final class TestOtherEdge extends OtherEdge<CSCallSite, CSMethod> {

        private TestOtherEdge(CSCallSite callSite, CSMethod callee) {
            super(callSite, callee);
        }
    }
}
