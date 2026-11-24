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

import pascal.taie.analysis.pta.pts.PointsToSetCensus;

import java.util.Arrays;

import static pascal.taie.analysis.pta.pts.PointsToSetCensus.BUCKETS;
import static pascal.taie.analysis.pta.pts.PointsToSetCensus.bucket;
import static pascal.taie.analysis.pta.pts.PointsToSetCensus.formatHistogram;

/**
 * Strongly connected components of a graph given in compressed sparse row
 * form: the successors of node {@code u} are
 * {@code targets[start[u] .. start[u + 1])}. Computed by an iterative
 * Tarjan (no recursion, so deep graphs do not overflow the stack) on
 * primitive arrays indexed by node.
 *
 * @param nodes           number of nodes
 * @param edges           number of edges
 * @param cyclicSccs      number of SCCs with more than one node
 * @param sizeHistogram   SCCs with more than one node by size, in log2
 *                        buckets (see {@link PointsToSetCensus#bucket(long)})
 * @param nodesInside     nodes inside SCCs with more than one node
 * @param edgesInside     edges whose ends lie in the same SCC with more
 *                        than one node
 * @param largest         size of the largest SCC (1 if all are trivial,
 *                        0 for an empty graph)
 */
record PfgSccCensus(int nodes, int edges, int cyclicSccs, long[] sizeHistogram,
                    long nodesInside, long edgesInside, int largest) {

    /**
     * @param start   successor offsets, length {@code nodes + 1}
     * @param targets successor nodes, length {@code start[nodes]}
     */
    static PfgSccCensus of(int[] start, int[] targets) {
        int n = start.length - 1;
        int[] order = new int[n]; // 0 = not visited, else visit number
        int[] low = new int[n];
        int[] comp = new int[n];
        Arrays.fill(comp, -1);
        boolean[] onStack = new boolean[n];
        int[] stack = new int[n];
        int sp = 0;
        int[] callNode = new int[n];
        int[] callEdge = new int[n];
        int[] compSize = new int[n];
        int counter = 0;
        int comps = 0;
        for (int root = 0; root < n; root++) {
            if (order[root] != 0) {
                continue;
            }
            order[root] = ++counter;
            low[root] = counter;
            stack[sp++] = root;
            onStack[root] = true;
            int cp = 0;
            callNode[cp] = root;
            callEdge[cp] = start[root];
            cp++;
            while (cp > 0) {
                int u = callNode[cp - 1];
                int e = callEdge[cp - 1];
                if (e < start[u + 1]) {
                    callEdge[cp - 1] = e + 1;
                    int v = targets[e];
                    if (order[v] == 0) {
                        order[v] = ++counter;
                        low[v] = counter;
                        stack[sp++] = v;
                        onStack[v] = true;
                        callNode[cp] = v;
                        callEdge[cp] = start[v];
                        cp++;
                    } else if (onStack[v]) {
                        low[u] = Math.min(low[u], order[v]);
                    }
                    continue;
                }
                cp--;
                if (cp > 0) {
                    int parent = callNode[cp - 1];
                    low[parent] = Math.min(low[parent], low[u]);
                }
                if (low[u] == order[u]) {
                    int size = 0;
                    int w;
                    do {
                        w = stack[--sp];
                        onStack[w] = false;
                        comp[w] = comps;
                        size++;
                    } while (w != u);
                    compSize[comps++] = size;
                }
            }
        }
        long[] histogram = new long[BUCKETS];
        int cyclic = 0;
        long inside = 0;
        int largest = 0;
        for (int c = 0; c < comps; c++) {
            int size = compSize[c];
            largest = Math.max(largest, size);
            if (size > 1) {
                cyclic++;
                inside += size;
                histogram[bucket(size)]++;
            }
        }
        long edgesInside = 0;
        for (int u = 0; u < n; u++) {
            int c = comp[u];
            if (compSize[c] > 1) {
                for (int e = start[u]; e < start[u + 1]; e++) {
                    if (comp[targets[e]] == c) {
                        edgesInside++;
                    }
                }
            }
        }
        return new PfgSccCensus(n, start[n], cyclic, histogram, inside, edgesInside, largest);
    }

    @Override
    public String toString() {
        return "pfg-scc nodes=" + nodes + " edges=" + edges
                + " cyclic-sccs=" + cyclicSccs + " pointers-inside=" + nodesInside
                + " edges-inside=" + edgesInside + " largest=" + largest
                + " sizes=" + formatHistogram(sizeHistogram);
    }
}
