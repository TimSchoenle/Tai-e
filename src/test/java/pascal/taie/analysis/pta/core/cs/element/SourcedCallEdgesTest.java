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

import java.lang.ref.Reference;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.ConcurrentModificationException;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.BiFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Sourced call edges ({@link SourcedEdge}) are held by call sites and CS
 * methods as their sources, and every reader sees the edges, their order
 * and their hash codes as an {@link OpenHashSet} and an insertion-ordered
 * list of the added edge objects give them, mixed with plain and other
 * edges.
 */
public class SourcedCallEdgesTest {

    private final Context context = new TrieContext.Factory<>().getEmptyContext();

    private final CSMethod caller = new CSMethod(null, context);

    @Test
    void sourcedEdgeIsRebuiltNotRetained() {
        CSCallSite site = virtualSite();
        CSMethod callee = new CSMethod(null, context);
        TestSource source = new TestSource(7, 1);
        Edge<CSCallSite, CSMethod> edge = source.edge(site, callee);
        assertTrue(site.addEdge(edge));
        callee.addEdge(edge);

        Edge<CSCallSite, CSMethod> out = site.getEdges().iterator().next();
        assertNotSame(edge, out);
        assertEquals(edge, out);
        assertEquals(edge.hashCode(), out.hashCode());
        assertSame(TestSourcedEdge.class, out.getClass());
        assertSame(source, ((SourcedEdge) out).getSource());

        Edge<CSCallSite, CSMethod> in = callee.getEdge(0);
        assertNotSame(edge, in);
        assertEquals(edge, in);
        assertSame(site, in.getCallSite());
        assertSame(callee, in.getCallee());

        assertFalse(site.addEdge(new TestSource(7, 1).edge(site, callee)),
                "an equal source is the same edge");
        assertTrue(site.addEdge(new TestSource(8, 1).edge(site, callee)),
                "another source with the same hash is another edge");
        assertTrue(site.addEdge(new Edge<>(CallKind.VIRTUAL, site, callee)));
        assertEquals(3, site.getEdges().size());
    }

    @Test
    void sourcedSecondEdgeAfterAPlainSingle() {
        CSCallSite site = virtualSite();
        CSMethod callee = new CSMethod(null, context);
        Edge<CSCallSite, CSMethod> plain = new Edge<>(CallKind.VIRTUAL, site, callee);
        Edge<CSCallSite, CSMethod> sourced = new TestSource(1, 1).edge(site, callee);
        assertTrue(site.addEdge(plain));
        assertTrue(site.addEdge(sourced));
        assertEquals(List.of(plain, sourced), List.copyOf(site.getEdges()));
        assertSame(TestSourcedEdge.class, List.copyOf(site.getEdges()).get(1).getClass());
        assertSame(Edge.class, List.copyOf(site.getEdges()).get(0).getClass());
    }

    @Test
    void incomingSourcedEdgesFailFastAndSplitAtTheirIndices() {
        CSMethod callee = new CSMethod(null, context);
        List<Edge<CSCallSite, CSMethod>> added = new ArrayList<>();
        for (int i = 0; i < 40; ++i) {
            CSCallSite site = virtualSite();
            Edge<CSCallSite, CSMethod> edge = i % 3 == 0
                    ? new Edge<>(CallKind.VIRTUAL, site, callee)
                    : new TestSource(i, i % 5).edge(site, callee);
            callee.addEdge(edge);
            added.add(edge);
        }
        List<Edge<CSCallSite, CSMethod>> view = callee.getEdges();
        assertEquals(added, view);
        assertEquals(added, view.stream().toList());
        assertEquals(added, view.parallelStream().toList());
        List<Edge<CSCallSite, CSMethod>> each = new ArrayList<>();
        view.forEach(each::add);
        assertEquals(added, each);
        for (int i = 0; i < added.size(); ++i) {
            assertSame(added.get(i).getClass(), view.get(i).getClass());
        }
        Runnable addOne = () -> callee.addEdge(
                new TestSource(99, 0).edge(virtualSite(), callee));
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
    void outgoingSourcedEdgesFailFast() {
        CSCallSite site = virtualSite();
        site.addEdge(new TestSource(1, 1).edge(site, new CSMethod(null, context)));
        site.addEdge(new TestSource(2, 1).edge(site, new CSMethod(null, context)));
        assertThrows(ConcurrentModificationException.class, () -> {
            for (Edge<CSCallSite, CSMethod> ignored : site.getEdges()) {
                site.addEdge(new TestSource(3, 1).edge(site, new CSMethod(null, context)));
            }
        });
    }

    @Test
    void readersSeeTheEdgesInTheOrderOfTheObjectStore() {
        for (long seed = 1; seed <= 16; ++seed) {
            checkAgainstObjectStore(new Random(seed), 2 + (int) seed * 25);
        }
    }

    /**
     * Bytes that a sourced edge adds to its call site and callee, against
     * the same edge held as its object (as an {@link OtherEdge} is), over
     * call sites and callees with eight edges each; the median of five
     * interleaved measurements of each, against GC noise. An edge object
     * takes 24 to 32 bytes, the parallel arrays about 6 bytes per edge.
     */
    @Test
    void sourcedEdgeTakesAtLeast12BytesLessThanItsObject() {
        TestSource source = new TestSource(1, 1);
        double[] held = new double[5];
        double[] sourced = new double[5];
        for (int i = 0; i < held.length; ++i) {
            held[i] = bytesPerEdge((site, callee) -> new TestOtherEdge(site, callee));
            sourced[i] = bytesPerEdge(source::edge);
        }
        Arrays.sort(held);
        Arrays.sort(sourced);
        double heldMedian = held[held.length / 2];
        double sourcedMedian = sourced[sourced.length / 2];
        System.out.println("[spd] bytes per edge: held as object " + heldMedian
                + ", held as source " + sourcedMedian);
        assertTrue(heldMedian - sourcedMedian >= 12,
                "held " + Arrays.toString(held) + " sourced " + Arrays.toString(sourced));
    }

    private double bytesPerEdge(
            BiFunction<CSCallSite, CSMethod, Edge<CSCallSite, CSMethod>> edges) {
        int fanOut = 8;
        int sites = 20_000;
        CSCallSite[] siteArray = new CSCallSite[sites];
        CSMethod[] callees = new CSMethod[sites];
        for (int i = 0; i < sites; ++i) {
            siteArray[i] = virtualSite();
            callees[i] = new CSMethod(null, context);
        }
        long before = usedAfterGc();
        for (int i = 0; i < sites; ++i) {
            for (int k = 0; k < fanOut; ++k) {
                CSMethod callee = callees[(i + k * 997) % sites];
                Edge<CSCallSite, CSMethod> edge = edges.apply(siteArray[i], callee);
                if (siteArray[i].addEdge(edge)) {
                    callee.addEdge(edge);
                }
            }
        }
        long used = usedAfterGc() - before;
        Reference.reachabilityFence(siteArray);
        Reference.reachabilityFence(callees);
        return (double) used / ((long) sites * fanOut);
    }

    private static long usedAfterGc() {
        Runtime runtime = Runtime.getRuntime();
        for (int i = 0; i < 3; ++i) {
            System.gc();
        }
        return runtime.totalMemory() - runtime.freeMemory();
    }

    /**
     * Adds a random stream of plain, other-kind, subclass, sourced (with
     * equal sources as distinct objects, and colliding hash codes) and
     * duplicate edges to call sites and their callees, and compares every
     * reader with an {@link OpenHashSet} per call site and a list per callee
     * that hold the added edge objects.
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
                assertSameEdges(siteRef, site.getEdges(), probes);
            }
        }
        for (CSCallSite site : sites) {
            assertSameEdges(outRef.getOrDefault(site, Set.of()), site.getEdges(), probes);
        }
        for (CSMethod callee : callees) {
            List<Edge<CSCallSite, CSMethod>> expected = inRef.getOrDefault(callee, List.of());
            assertEquals(expected, callee.getEdges());
            assertEquals(expected, callee.getEdges().stream().toList());
            assertEquals(expected.size(), callee.getEdgeCount());
            for (int i = 0; i < expected.size(); ++i) {
                assertEquals(expected.get(i), callee.getEdge(i));
                assertEquals(expected.get(i).hashCode(), callee.getEdge(i).hashCode());
                assertSame(expected.get(i).getClass(), callee.getEdge(i).getClass());
            }
        }
    }

    private static void assertSameEdges(Set<Edge<CSCallSite, CSMethod>> expected,
                                        Set<Edge<CSCallSite, CSMethod>> actual,
                                        List<Edge<CSCallSite, CSMethod>> probes) {
        assertEquals(expected.size(), actual.size());
        List<Edge<CSCallSite, CSMethod>> expectedList = List.copyOf(expected);
        List<Edge<CSCallSite, CSMethod>> actualList = List.copyOf(actual);
        assertEquals(expectedList, actualList);
        for (int i = 0; i < expectedList.size(); ++i) {
            assertEquals(expectedList.get(i).hashCode(), actualList.get(i).hashCode());
            assertSame(expectedList.get(i).getClass(), actualList.get(i).getClass());
        }
        for (Edge<CSCallSite, CSMethod> probe : probes) {
            assertEquals(expected.contains(probe), actual.contains(probe));
        }
    }

    private Edge<CSCallSite, CSMethod> randomEdge(
            Random random, CSCallSite site, CSMethod callee) {
        int pick = random.nextInt(12);
        if (pick == 0) {
            return new Edge<>(CallKind.OTHER, site, callee);
        } else if (pick == 1) {
            return new TestOtherEdge(site, callee);
        } else if (pick == 2) {
            return new Edge<>(CallKind.VIRTUAL, site, callee);
        } else if (pick <= 7) {
            // few ids, so equal sources recur as distinct objects; few
            // hash values, so different sources collide
            int id = random.nextInt(4);
            return new TestSource(id, id % 2).edge(site, callee);
        }
        CallKind kind = site.getCallSite() == null
                ? CallKind.STATIC
                : CallGraphs.getCallKind(site.getCallSite());
        return new Edge<>(kind, site, callee);
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

    /**
     * A source whose equality is its id and whose hash is {@code hash}, so
     * that sources may collide.
     */
    private record TestSource(int id, int hash) implements EdgeSource {

        @Override
        public Edge<CSCallSite, CSMethod> edge(CSCallSite callSite, CSMethod callee) {
            return new TestSourcedEdge(callSite, callee, this);
        }

        @Override
        public int edgeHashCode(CSCallSite callSite, CSMethod callee) {
            return new Edge<>(CallKind.OTHER, callSite, callee).hashCode() * 31 + hash;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof TestSource that && id == that.id;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    private static final class TestSourcedEdge extends OtherEdge<CSCallSite, CSMethod>
            implements SourcedEdge {

        private final TestSource source;

        private TestSourcedEdge(CSCallSite callSite, CSMethod callee, TestSource source) {
            super(callSite, callee);
            this.source = source;
        }

        @Override
        public EdgeSource getSource() {
            return source;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof TestSourcedEdge that && super.equals(o)
                    && source.equals(that.source);
        }

        @Override
        public int hashCode() {
            return super.hashCode() * 31 + source.hash();
        }
    }
}
