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

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class PfgSccCensusTest {

    /**
     * Builds the compressed sparse row form of a graph from
     * {@code {source, target}} pairs.
     */
    private static PfgSccCensus census(int nodes, int[]... edges) {
        List<List<Integer>> succs = new ArrayList<>();
        for (int i = 0; i < nodes; i++) {
            succs.add(new ArrayList<>());
        }
        for (int[] e : edges) {
            succs.get(e[0]).add(e[1]);
        }
        int[] start = new int[nodes + 1];
        int[] targets = new int[edges.length];
        int k = 0;
        for (int u = 0; u < nodes; u++) {
            for (int v : succs.get(u)) {
                targets[k++] = v;
            }
            start[u + 1] = k;
        }
        return PfgSccCensus.of(start, targets);
    }

    @Test
    void countsKnownSccs() {
        // {0,1,2} (with the chord 0->2), {3,4}, {6,7,8,9} as a ring with a
        // chord; 5 has a self loop; 10 and 11 are on no cycle
        PfgSccCensus c = census(12,
                new int[]{0, 1}, new int[]{1, 2}, new int[]{2, 0}, new int[]{0, 2},
                new int[]{2, 3}, new int[]{3, 4}, new int[]{4, 3},
                new int[]{5, 5}, new int[]{4, 5},
                new int[]{6, 7}, new int[]{7, 8}, new int[]{8, 9}, new int[]{9, 6},
                new int[]{7, 9},
                new int[]{10, 6}, new int[]{9, 11});
        assertEquals(12, c.nodes());
        assertEquals(16, c.edges());
        assertEquals(3, c.cyclicSccs());
        assertEquals(9, c.nodesInside());
        // 4 in {0,1,2}, 2 in {3,4}, 5 in {6..9}; the self loop is outside
        assertEquals(11, c.edgesInside());
        assertEquals(4, c.largest());
        long[] expected = new long[c.sizeHistogram().length];
        expected[2] = 2; // sizes 2 and 3
        expected[3] = 1; // size 4
        assertEquals(toList(expected), toList(c.sizeHistogram()));
        assertEquals("pfg-scc nodes=12 edges=16 cyclic-sccs=3 pointers-inside=9"
                + " edges-inside=11 largest=4 sizes={[2,3]=2, [4,7]=1}", c.toString());
    }

    @Test
    void acyclicGraphHasNoCyclicScc() {
        PfgSccCensus c = census(4, new int[]{0, 1}, new int[]{1, 2}, new int[]{0, 3});
        assertEquals(0, c.cyclicSccs());
        assertEquals(0, c.nodesInside());
        assertEquals(0, c.edgesInside());
        assertEquals(1, c.largest());
    }

    @Test
    void emptyGraph() {
        PfgSccCensus c = PfgSccCensus.of(new int[]{0}, new int[0]);
        assertEquals(0, c.nodes());
        assertEquals(0, c.cyclicSccs());
        assertEquals(0, c.largest());
    }

    /**
     * A ring far deeper than a recursive Tarjan could walk on the default
     * thread stack.
     */
    @Test
    void deepRingIsOneScc() {
        int n = 1_000_000;
        int[] start = new int[n + 1];
        int[] targets = new int[n];
        for (int u = 0; u < n; u++) {
            start[u + 1] = u + 1;
            targets[u] = (u + 1) % n;
        }
        PfgSccCensus c = PfgSccCensus.of(start, targets);
        assertEquals(1, c.cyclicSccs());
        assertEquals(n, c.nodesInside());
        assertEquals(n, c.edgesInside());
        assertEquals(n, c.largest());
        assertEquals(1, c.sizeHistogram()[20]); // 2^19 <= n < 2^20
    }

    private static List<Long> toList(long[] values) {
        List<Long> list = new ArrayList<>();
        for (long v : values) {
            list.add(v);
        }
        return list;
    }
}
