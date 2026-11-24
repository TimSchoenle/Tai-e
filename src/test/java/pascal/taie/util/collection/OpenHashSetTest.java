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

package pascal.taie.util.collection;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.callgraph.OtherEdge;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Equivalence of {@link OpenHashSet} with the hybrid set it replaces as the
 * call-edge set of a context-sensitive call site ({@link HybridHashSet}):
 * both receive the same edge streams and must agree on every add result,
 * on contents and size after every step, on contains for present and
 * absent edges, and on iteration order while the set is small.
 */
class OpenHashSetTest {

    /** Identity-hashed node, as CSCallSite, CSMethod and contexts are. */
    private static final class Node {
        private final int id;

        Node(int id) {
            this.id = id;
        }

        @Override
        public String toString() {
            return "n" + id;
        }
    }

    /** Node whose hash always collides, to force long probe chains. */
    private static final class Colliding {
        private final int id;

        Colliding(int id) {
            this.id = id;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Colliding c && c.id == id;
        }

        @Override
        public int hashCode() {
            return 7;
        }
    }

    /**
     * Same equality shape as LambdaCallEdge: an OTHER edge whose identity
     * also includes the lambda's indy and context, hash recomputed per call.
     */
    private static final class LambdaLikeEdge extends OtherEdge<Object, Object> {
        private final Object indy;
        private final Object context;

        LambdaLikeEdge(Object site, Object callee, Object indy, Object context) {
            super(site, callee);
            this.indy = indy;
            this.context = context;
        }

        @Override
        public boolean equals(Object o) {
            return super.equals(o) && o instanceof LambdaLikeEdge that
                    && indy.equals(that.indy) && context.equals(that.context);
        }

        @Override
        public int hashCode() {
            return Objects.hash(super.hashCode(), indy, context);
        }
    }

    /** Plain OTHER edge of another class than the lambda one. */
    private static final class PlainOtherEdge extends OtherEdge<Object, Object> {
        PlainOtherEdge(Object site, Object callee) {
            super(site, callee);
        }
    }

    private static final CallKind[] KINDS = {
            CallKind.VIRTUAL, CallKind.INTERFACE, CallKind.STATIC, CallKind.SPECIAL};

    /** Feeds the stream to both sets and compares them after every add. */
    private static void assertEquivalent(List<Edge<Object, Object>> stream) {
        Set<Edge<Object, Object>> reference = new HybridHashSet<>();
        Set<Edge<Object, Object>> set = new OpenHashSet<>();
        // the hybrid set turns into a HashSet on any add at size 8, also a
        // duplicate one; until then both iterate in insertion order
        boolean referenceHashed = false;
        for (Edge<Object, Object> e : stream) {
            referenceHashed |= reference.size() == OpenHashSet.SMALL_LIMIT;
            assertEquals(reference.add(e), set.add(e), () -> "add " + e);
            assertEquals(reference.size(), set.size());
            assertTrue(set.contains(e));
            if (!referenceHashed) {
                assertEquals(new ArrayList<>(reference), new ArrayList<>(set),
                        "small sets iterate in insertion order");
            }
        }
        assertEquals(reference, set);
        assertEquals(set, reference);
        List<Edge<Object, Object>> iterated = new ArrayList<>(set);
        assertEquals(set.size(), iterated.size());
        assertEquals(new HashSet<>(reference), new HashSet<>(iterated));
        for (Edge<Object, Object> e : stream) {
            assertTrue(set.contains(e));
        }
    }

    private static List<Edge<Object, Object>> randomStream(Random random, int length,
                                                           int sites, int callees) {
        Object[] siteNodes = new Object[sites];
        Object[] calleeNodes = new Object[callees];
        for (int i = 0; i < sites; ++i) {
            siteNodes[i] = random.nextInt(4) == 0 ? new Colliding(i) : new Node(i);
        }
        for (int i = 0; i < callees; ++i) {
            calleeNodes[i] = new Node(1000 + i);
        }
        Object[] indys = {new Node(-1), new Node(-2)};
        Object[] contexts = {new Node(-3), new Node(-4), new Node(-5)};
        List<Edge<Object, Object>> stream = new ArrayList<>();
        for (int i = 0; i < length; ++i) {
            Object site = siteNodes[random.nextInt(sites)];
            Object callee = calleeNodes[random.nextInt(callees)];
            Edge<Object, Object> e = switch (random.nextInt(4)) {
                case 0 -> new LambdaLikeEdge(site, callee,
                        indys[random.nextInt(indys.length)],
                        contexts[random.nextInt(contexts.length)]);
                case 1 -> new PlainOtherEdge(site, callee);
                default -> new Edge<>(KINDS[random.nextInt(KINDS.length)], site, callee);
            };
            stream.add(e);
            if (random.nextInt(3) == 0) { // a fresh but equal duplicate
                stream.add(copyOf(e));
            }
        }
        return stream;
    }

    private static Edge<Object, Object> copyOf(Edge<Object, Object> e) {
        if (e instanceof LambdaLikeEdge l) {
            return new LambdaLikeEdge(l.getCallSite(), l.getCallee(), l.indy, l.context);
        } else if (e instanceof PlainOtherEdge) {
            return new PlainOtherEdge(e.getCallSite(), e.getCallee());
        }
        return new Edge<>(e.getKind(), e.getCallSite(), e.getCallee());
    }

    @Test
    void randomStreamsAroundTheSmallLimit() {
        Random random = new Random(20261124L);
        for (int round = 0; round < 400; ++round) {
            int length = random.nextInt(24);
            assertEquivalent(randomStream(random, length, 1 + random.nextInt(3),
                    1 + random.nextInt(12)));
        }
    }

    @Test
    void randomLargeStreams() {
        Random random = new Random(7L);
        for (int round = 0; round < 20; ++round) {
            assertEquivalent(randomStream(random, 3000, 1 + random.nextInt(4),
                    50 + random.nextInt(600)));
        }
    }

    @Test
    void recordedStreamLambdaEdgesWithEqualCalleeStayDistinct() {
        Node site = new Node(1);
        Node callee = new Node(2);
        Node indyA = new Node(3);
        Node indyB = new Node(4);
        Node ctxA = new Node(5);
        Node ctxB = new Node(6);
        List<Edge<Object, Object>> stream = new ArrayList<>();
        stream.add(new Edge<>(CallKind.INTERFACE, site, callee));
        stream.add(new LambdaLikeEdge(site, callee, indyA, ctxA));
        stream.add(new LambdaLikeEdge(site, callee, indyA, ctxB));
        stream.add(new LambdaLikeEdge(site, callee, indyB, ctxA));
        stream.add(new LambdaLikeEdge(site, callee, indyA, ctxA));
        stream.add(new PlainOtherEdge(site, callee));
        stream.add(new Edge<>(CallKind.VIRTUAL, site, callee));
        stream.add(new Edge<>(CallKind.INTERFACE, site, callee));
        for (int i = 0; i < 12; ++i) { // cross the small limit, then repeat all
            stream.add(new Edge<>(CallKind.VIRTUAL, site, new Node(100 + i)));
        }
        stream.addAll(new ArrayList<>(stream));
        assertEquivalent(stream);
        Set<Edge<Object, Object>> set = new OpenHashSet<>();
        stream.forEach(set::add);
        // INTERFACE, three distinct lambda edges, plain OTHER, VIRTUAL, 12 more
        assertEquals(6 + 12, set.size());
    }

    @Test
    void sizesAroundTheSmallLimitIterateExactlyOnce() {
        for (int n = 0; n <= 40; ++n) {
            OpenHashSet<Object> set = new OpenHashSet<>();
            List<Object> added = new ArrayList<>();
            for (int i = 0; i < n; ++i) {
                Object o = i % 2 == 0 ? new Colliding(i) : new Node(i);
                assertTrue(set.add(o));
                assertFalse(set.add(o));
                added.add(o);
            }
            List<Object> iterated = new ArrayList<>(set);
            assertEquals(n, iterated.size());
            assertEquals(new HashSet<>(added), new HashSet<>(iterated));
            assertFalse(set.contains(new Node(-1)));
            assertFalse(set.contains(new Colliding(-1)));
            assertFalse(set.contains(null));
            Iterator<Object> it = set.iterator();
            iterated.forEach(o -> it.next());
            assertThrows(NoSuchElementException.class, it::next);
        }
    }

    @Test
    void addDuringIterationFailsFast() {
        for (int n : new int[] {1, 2, 8, 9, 30}) {
            OpenHashSet<Object> set = new OpenHashSet<>();
            for (int i = 0; i < n; ++i) {
                set.add(new Node(i));
            }
            Iterator<Object> it = set.iterator();
            it.next();
            set.add(new Node(-1));
            assertThrows(java.util.ConcurrentModificationException.class, it::next,
                    () -> "size " + n);
        }
    }

    @Test
    void rejectsNullAndRemoval() {
        OpenHashSet<Object> set = new OpenHashSet<>();
        assertThrows(NullPointerException.class, () -> set.add(null));
        set.add(new Node(1));
        Iterator<Object> it = set.iterator();
        it.next();
        assertThrows(UnsupportedOperationException.class, it::remove);
    }
}
