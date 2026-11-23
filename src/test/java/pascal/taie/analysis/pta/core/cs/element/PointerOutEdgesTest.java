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
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.solver.Identity;
import pascal.taie.analysis.pta.core.solver.OtherEdge;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.core.solver.Transfer;
import pascal.taie.analysis.pta.core.solver.TypeFilter;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.IntType;
import pascal.taie.language.type.LongType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.ArraySet;
import pascal.taie.util.collection.HybridIndexableSet;

import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The out edges of an {@link AbstractPointer}, some stored without edge
 * objects, behave as the list of edge objects they replace: every addition,
 * removal and iteration gives what {@link ListPointer} (that list, with the
 * default {@link Pointer#addEdge(PointerFlowEdge, Transfer)} and
 * {@link Pointer#forEachOutTransfer}) gives.
 */
class PointerOutEdgesTest {

    private static final int TARGETS = 40;

    private static final FlowKind[] KINDS = FlowKind.values();

    /**
     * A pointer that holds its out edges as objects in a list.
     */
    private static final class ListPointer implements Pointer {

        private final Set<Pointer> successors = new HybridIndexableSet<>(true);

        private final ArrayList<PointerFlowEdge> outEdges = new ArrayList<>();

        @Override
        public int getIndex() {
            return TARGETS + 1;
        }

        @Override
        public PointsToSet getPointsToSet() {
            return null;
        }

        @Override
        public void setPointsToSet(PointsToSet pointsToSet) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void addFilter(Predicate<CSObj> filter) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Set<Predicate<CSObj>> getFilters() {
            return Set.of();
        }

        @Override
        public Set<CSObj> getObjects() {
            return Set.of();
        }

        @Override
        public Stream<CSObj> objects() {
            return Stream.of();
        }

        @Override
        public PointerFlowEdge addEdge(PointerFlowEdge edge) {
            if (successors.add(edge.target())) {
                outEdges.add(edge);
                return edge;
            } else if (edge.kind() == FlowKind.OTHER) {
                for (PointerFlowEdge outEdge : outEdges) {
                    if (outEdge.equals(edge)) {
                        return outEdge;
                    }
                }
                outEdges.add(edge);
                return edge;
            }
            return null;
        }

        @Override
        public void removeEdgesIf(Predicate<PointerFlowEdge> filter) {
            outEdges.removeIf(filter);
        }

        @Override
        public Set<PointerFlowEdge> getOutEdges() {
            return Collections.unmodifiableSet(new ArraySet<>(outEdges, true));
        }

        @Override
        public int getOutDegree() {
            return outEdges.size();
        }

        @Override
        public Type getType() {
            return null;
        }
    }

    private static final class TestPointer extends AbstractPointer {

        TestPointer(int index) {
            super(index);
        }

        @Override
        public Type getType() {
            return null;
        }

        @Override
        public String toString() {
            return "p" + getIndex();
        }
    }

    private static final class Other extends OtherEdge {
        Other(Pointer source, Pointer target) {
            super(source, target);
        }
    }

    /**
     * A subclass of a kind other than OTHER: stored as an object.
     */
    private static final class Plain extends PointerFlowEdge {
        Plain(FlowKind kind, Pointer source, Pointer target) {
            super(kind, source, target);
        }
    }

    /**
     * A transfer that may read the edge: stored as an object.
     */
    private record Custom(int id) implements Transfer {
        @Override
        public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
            return input;
        }
    }

    private static TypeFilter typeFilter(Type type) {
        Object manager = Proxy.newProxyInstance(PointerOutEdgesTest.class.getClassLoader(),
                new Class<?>[]{CSManager.class}, (proxy, method, args) -> null);
        Solver solver = (Solver) Proxy.newProxyInstance(PointerOutEdgesTest.class.getClassLoader(),
                new Class<?>[]{Solver.class},
                (proxy, method, args) -> method.getName().equals("getCSManager") ? manager : null);
        return new TypeFilter(type, solver);
    }

    private static final Pointer[] TARGET = new Pointer[TARGETS];

    static {
        for (int i = 0; i < TARGETS; i++) {
            TARGET[i] = new TestPointer(i);
        }
    }

    private final Transfer[] transfers = {
            Identity.get(), typeFilter(IntType.INT), typeFilter(LongType.LONG),
            new Custom(1), new Custom(2)};

    /**
     * Builds the same edge for either source.
     */
    private record EdgeSpec(int shape, FlowKind kind, int target, Transfer preset) {
        PointerFlowEdge build(Pointer source) {
            PointerFlowEdge edge = switch (shape) {
                case 0 -> new PointerFlowEdge(kind, source, TARGET[target]);
                case 1 -> new Plain(kind, source, TARGET[target]);
                default -> new Other(source, TARGET[target]);
            };
            if (preset != null) {
                edge.addTransfer(preset);
            }
            return edge;
        }
    }

    private EdgeSpec randomEdge(Random random) {
        int shape = random.nextInt(10) < 7 ? 0 : 1 + random.nextInt(2);
        FlowKind kind = KINDS[random.nextInt(KINDS.length)];
        Transfer preset = random.nextInt(10) == 0 ? randomTransfer(random) : null;
        return new EdgeSpec(shape, kind, random.nextInt(TARGETS), preset);
    }

    private Transfer randomTransfer(Random random) {
        return transfers[random.nextInt(transfers.length)];
    }

    /**
     * @return the class, kind, target and transfers of the edge, or null.
     */
    private static List<Object> describe(PointerFlowEdge edge) {
        if (edge == null) {
            return null;
        }
        List<Object> d = new ArrayList<>();
        d.add(edge.getClass());
        d.add(edge.kind());
        d.add(edge.target());
        edge.forEachTransfer(d::add);
        return d;
    }

    private static List<List<Object>> outEdges(Pointer pointer) {
        List<List<Object>> all = new ArrayList<>();
        for (PointerFlowEdge edge : pointer.getOutEdges()) {
            assertSame(pointer, edge.source());
            all.add(describe(edge));
        }
        return all;
    }

    private static List<Object> outTransfers(Pointer pointer, boolean compact) {
        List<Object> all = new ArrayList<>();
        pointer.forEachOutTransfer((edge, target, transfer) -> {
            if (edge == null) {
                assertTrue(compact);
                assertTrue(transfer == Identity.get() || transfer.getClass() == TypeFilter.class);
            } else {
                assertSame(target, edge.target());
            }
            all.add(target);
            all.add(transfer);
        });
        return all;
    }

    private static void assertSameEdges(Pointer expected, Pointer actual) {
        assertEquals(outEdges(expected), outEdges(actual));
        assertEquals(expected.getOutDegree(), actual.getOutDegree());
        assertEquals(outTransfers(expected, false), outTransfers(actual, true));
    }

    @Test
    void randomOperationsMatchTheListOfEdgeObjects() {
        for (int seed = 0; seed < 300; seed++) {
            Random random = new Random(seed);
            ListPointer expected = new ListPointer();
            TestPointer actual = new TestPointer(TARGETS);
            for (int step = 0; step < 200; step++) {
                int op = random.nextInt(20);
                if (op < 14) {
                    EdgeSpec spec = randomEdge(random);
                    Transfer transfer = randomTransfer(random);
                    PointerFlowEdge want = expected.addEdge(spec.build(expected), transfer);
                    PointerFlowEdge got = actual.addEdge(spec.build(actual), transfer);
                    assertEquals(describe(want), describe(got), "seed " + seed + " step " + step);
                } else if (op < 19) {
                    EdgeSpec spec = randomEdge(random);
                    PointerFlowEdge passedWant = spec.build(expected);
                    PointerFlowEdge passedGot = spec.build(actual);
                    PointerFlowEdge want = expected.addEdge(passedWant);
                    PointerFlowEdge got = actual.addEdge(passedGot);
                    assertEquals(describe(want), describe(got), "seed " + seed + " step " + step);
                    assertEquals(want == passedWant, got == passedGot);
                    if (want != null && random.nextBoolean()) {
                        Transfer transfer = randomTransfer(random);
                        assertEquals(want.addTransfer(transfer), got.addTransfer(transfer));
                    }
                } else {
                    int mod = 2 + random.nextInt(3);
                    int rest = random.nextInt(mod);
                    Predicate<PointerFlowEdge> filter = random.nextBoolean()
                            ? e -> e.kind().ordinal() % mod == rest
                            : e -> e.target().getIndex() % mod == rest;
                    expected.removeEdgesIf(filter);
                    actual.removeEdgesIf(filter);
                }
                assertSameEdges(expected, actual);
            }
        }
    }

    @Test
    void everyKindAndTransferIsKeptAsAdded() {
        for (FlowKind kind : KINDS) {
            for (Transfer transfer : transfers) {
                for (int shape = 0; shape < 3; shape++) {
                    ListPointer expected = new ListPointer();
                    TestPointer actual = new TestPointer(TARGETS);
                    EdgeSpec spec = new EdgeSpec(shape, kind, 3, null);
                    PointerFlowEdge want = expected.addEdge(spec.build(expected), transfer);
                    PointerFlowEdge got = actual.addEdge(spec.build(actual), transfer);
                    assertEquals(describe(want), describe(got));
                    assertSameEdges(expected, actual);
                    // a second addition to the same target
                    assertEquals(describe(expected.addEdge(spec.build(expected), transfer)),
                            describe(actual.addEdge(spec.build(actual), transfer)));
                    assertSameEdges(expected, actual);
                }
            }
        }
    }

    @Test
    void identityAndTypeFilterEdgesAreStoredWithoutTheEdgeObject() {
        for (Transfer transfer : new Transfer[]{Identity.get(), transfers[1]}) {
            TestPointer pointer = new TestPointer(TARGETS);
            PointerFlowEdge edge = new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, pointer, TARGET[0]);
            assertSame(edge, pointer.addEdge(edge, transfer));
            PointerFlowEdge stored = pointer.getOutEdges().iterator().next();
            assertNotSame(edge, stored);
            assertEquals(describe(edge), describe(stored));
        }
    }

    @Test
    void otherSubclassAndCustomTransferEdgesAreStoredAsObjects() {
        TestPointer pointer = new TestPointer(TARGETS);
        PointerFlowEdge custom = new PointerFlowEdge(FlowKind.CAST, pointer, TARGET[0]);
        PointerFlowEdge plain = new Plain(FlowKind.LOCAL_ASSIGN, pointer, TARGET[1]);
        PointerFlowEdge other = new Other(pointer, TARGET[2]);
        PointerFlowEdge preset = new PointerFlowEdge(FlowKind.RETURN, pointer, TARGET[3]);
        preset.addTransfer(new Custom(3));
        assertSame(custom, pointer.addEdge(custom, new Custom(1)));
        assertSame(plain, pointer.addEdge(plain, Identity.get()));
        assertSame(other, pointer.addEdge(other, Identity.get()));
        assertSame(preset, pointer.addEdge(preset, Identity.get()));
        assertEquals(List.of(custom, plain, other, preset), new ArrayList<>(pointer.getOutEdges()));
    }

    @Test
    void aFilterThatThrowsLeavesTheEdgesUnchanged() {
        ListPointer expected = new ListPointer();
        TestPointer actual = new TestPointer(TARGETS);
        for (int t = 0; t < 8; t++) {
            EdgeSpec spec = new EdgeSpec(t % 3 == 0 ? 2 : 0, FlowKind.LOCAL_ASSIGN, t, null);
            expected.addEdge(spec.build(expected), Identity.get());
            actual.addEdge(spec.build(actual), Identity.get());
        }
        for (Pointer pointer : new Pointer[]{expected, actual}) {
            int[] seen = {0};
            assertThrows(IllegalStateException.class, () -> pointer.removeEdgesIf(e -> {
                if (++seen[0] == 6) {
                    throw new IllegalStateException();
                }
                return e.target().getIndex() % 2 == 0;
            }));
        }
        assertSameEdges(expected, actual);
    }

    @Test
    void anOtherEdgeEqualToAStoredEdgeReturnsAnEdgeThatKeepsItsTransfers() {
        TestPointer pointer = new TestPointer(TARGETS);
        pointer.addEdge(new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, pointer, TARGET[0]), Identity.get());
        PointerFlowEdge existing = pointer.addEdge(
                new PointerFlowEdge(FlowKind.OTHER, pointer, TARGET[0]));
        assertNotNull(existing);
        assertEquals(FlowKind.LOCAL_ASSIGN, existing.kind());
        Transfer added = new Custom(7);
        assertTrue(existing.addTransfer(added));
        PointerFlowEdge stored = pointer.getOutEdges().iterator().next();
        assertSame(existing, stored);
        assertEquals(List.of(PointerFlowEdge.class, FlowKind.LOCAL_ASSIGN, TARGET[0],
                Identity.get(), added), describe(stored));
        assertNull(pointer.addEdge(
                new PointerFlowEdge(FlowKind.CAST, pointer, TARGET[0]), Identity.get()));
    }
}
