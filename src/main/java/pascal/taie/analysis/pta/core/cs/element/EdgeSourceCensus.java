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

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

/**
 * The census of the sources of the sourced call edges (see
 * {@link EdgeSource}), taken over the CS methods given to {@link #add} and
 * the call sites of their incoming edges: per call site with sourced edges,
 * the number of its distinct sources (by identity); the bytes of the source
 * stores of the call sites (forward) and of the CS methods (reverse), each
 * beside the bytes of the layout without codes and sparse stores (forward:
 * an {@code EdgeSource[]} as long as the edge table; reverse: the shortest
 * dense {@code EdgeSource[]}). Bytes are estimates for 16-byte array
 * headers and 8-byte alignment. The census only reads the stores.
 */
public final class EdgeSourceCensus {

    private static final int[] DISTINCT_BOUNDS = {1, 8, 255, 65535};

    private static final String[] DISTINCT_NAMES = {"1", "2-8", "9-255", "256-65535", "more"};

    private final Set<CSCallSite> seen = Collections.newSetFromMap(new IdentityHashMap<>());

    private final long[] sitesByDistinct = new long[DISTINCT_NAMES.length];

    private long sites;

    private long forwardEdges;

    private int maxDistinct;

    private long forwardBytes;

    private long forwardRefBytes;

    private long callees;

    private long reverseEdges;

    private long reverseBytes;

    private long reverseDenseBytes;

    /**
     * Adds the sources of {@code callee} and of the call sites of its
     * incoming edges (each call site once per census).
     */
    public void add(CSMethod callee) {
        callee.census(this);
    }

    /**
     * Adds the sources of {@code site} if it was not added before.
     */
    void callSite(CSCallSite site) {
        if (seen.add(site)) {
            site.census(this);
        }
    }

    /**
     * Records a call site with {@code sourced} sourced edges of
     * {@code distinct} distinct sources, whose source store takes
     * {@code bytes}, and an {@code EdgeSource[]} as long as its table
     * {@code refBytes}.
     */
    void site(int sourced, int distinct, long bytes, long refBytes) {
        ++sites;
        forwardEdges += sourced;
        maxDistinct = Math.max(maxDistinct, distinct);
        int bucket = 0;
        while (bucket < DISTINCT_BOUNDS.length && distinct > DISTINCT_BOUNDS[bucket]) {
            ++bucket;
        }
        ++sitesByDistinct[bucket];
        forwardBytes += bytes;
        forwardRefBytes += refBytes;
    }

    /**
     * Records a CS method with {@code sourced} sourced incoming edges,
     * whose source store takes {@code bytes}, and the shortest dense one
     * {@code denseBytes}.
     */
    void callee(int sourced, long bytes, long denseBytes) {
        ++callees;
        reverseEdges += sourced;
        reverseBytes += bytes;
        reverseDenseBytes += denseBytes;
    }

    /**
     * @return the estimated bytes of an array of {@code length} elements
     * of {@code elementBytes} each; 0 for an empty array, as the stores
     * share one empty array of each type.
     */
    static long arrayBytes(long length, int elementBytes) {
        if (length == 0) {
            return 0;
        }
        return (16 + length * elementBytes + 7) & ~7L;
    }

    long forwardBytes() {
        return forwardBytes;
    }

    long forwardRefBytes() {
        return forwardRefBytes;
    }

    long reverseBytes() {
        return reverseBytes;
    }

    long reverseDenseBytes() {
        return reverseDenseBytes;
    }

    @Override
    public String toString() {
        StringBuilder line = new StringBuilder("edge-source census:")
                .append(" sites=").append(sites)
                .append(" forward_edges=").append(forwardEdges)
                .append(" distinct_per_site(");
        for (int i = 0; i < DISTINCT_NAMES.length; ++i) {
            line.append(i == 0 ? "" : " ").append(DISTINCT_NAMES[i])
                    .append('=').append(sitesByDistinct[i]);
        }
        return line.append(") max_distinct=").append(maxDistinct)
                .append(" forward_bytes=").append(forwardBytes)
                .append(" forward_ref_bytes=").append(forwardRefBytes)
                .append(" callees=").append(callees)
                .append(" reverse_edges=").append(reverseEdges)
                .append(" reverse_bytes=").append(reverseBytes)
                .append(" reverse_dense_bytes=").append(reverseDenseBytes)
                .toString();
    }
}
