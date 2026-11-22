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
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.util.collection.HybridHashSet;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The transfers of a {@link PointerFlowEdge} behave as the hybrid set they
 * are stored in place of: equal transfers are kept once, and iteration
 * follows the order of a {@link HybridHashSet} given the same additions.
 */
class PointerFlowEdgeTest {

    /**
     * A transfer with value equality, so that equal but distinct instances
     * exercise the duplicate rule.
     */
    private record Named(int id) implements Transfer {
        @Override
        public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
            return input;
        }
    }

    private static PointerFlowEdge newEdge() {
        return new PointerFlowEdge(FlowKind.LOCAL_ASSIGN, null, null);
    }

    private static List<Transfer> iterated(PointerFlowEdge edge) {
        List<Transfer> order = new ArrayList<>();
        edge.forEachTransfer(order::add);
        return order;
    }

    @Test
    void emptyEdgeHasNoTransfers() {
        PointerFlowEdge edge = newEdge();
        assertTrue(edge.getTransfers().isEmpty());
        assertTrue(iterated(edge).isEmpty());
    }

    @Test
    void equalTransfersAreKeptOnce() {
        for (int n = 1; n <= 20; n++) {
            PointerFlowEdge edge = newEdge();
            for (int i = 0; i < n; i++) {
                assertTrue(edge.addTransfer(new Named(i)));
            }
            for (int i = 0; i < n; i++) {
                assertFalse(edge.addTransfer(new Named(i)), "duplicate " + i + " of " + n);
            }
            assertEquals(n, edge.getTransfers().size());
            assertEquals(n, iterated(edge).size());
        }
    }

    @Test
    void iterationOrderIsTheOrderOfAHybridHashSet() {
        for (int n = 1; n <= 40; n++) {
            PointerFlowEdge edge = newEdge();
            Set<Transfer> expected = new HybridHashSet<>();
            // identity transfers (distinct objects): hash order differs from insertion order
            for (int i = 0; i < n; i++) {
                Transfer t = new Transfer() {
                    @Override
                    public PointsToSet apply(PointerFlowEdge e, PointsToSet input) {
                        return input;
                    }
                };
                assertEquals(expected.add(t), edge.addTransfer(t));
                // re-adding an earlier transfer must not change the order
                Transfer again = expected.iterator().next();
                assertEquals(expected.add(again), edge.addTransfer(again));
            }
            assertEquals(n, expected.size());
            assertEquals(new ArrayList<>(expected), iterated(edge), "order with " + n + " transfers");
            assertEquals(new ArrayList<>(expected), new ArrayList<>(edge.getTransfers()));
        }
    }

    @Test
    void transfersViewIsUnmodifiable() {
        PointerFlowEdge edge = newEdge();
        edge.addTransfer(new Named(1));
        assertThrows(UnsupportedOperationException.class,
                () -> edge.getTransfers().add(new Named(2)));
    }

    @Test
    void nullTransferIsRefused() {
        assertThrows(NullPointerException.class, () -> newEdge().addTransfer(null));
    }
}
