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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.pts.PointsToSet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicLongArray;

/**
 * Applies the transfers of the out-edges of one pointer to the delta that
 * the solver propagates from it, applying each {@link TypeFilter} once per
 * delta: the out-edges carrying the same filter get the same result object.
 * <p>
 * This is sound and changes no result: a type filter's result depends only
 * on its guard type and its input (it ignores the edge; its memo only caches
 * type checks), so the result for every further edge would be equal in
 * contents, iteration order and representation. The solver's consumers only
 * read the passed set: {@link WorkList#addFanOutEntry} copies it into a new
 * entry (once per fan-out) or adds it to an existing one, as it already does
 * for the delta itself,
 * which {@link Identity} passes to every identity edge. Only
 * {@code TypeFilter} itself is shared, not a subclass, which might depend
 * on the edge. The order of the solver's calls (edges, then transfers per
 * edge) is unchanged.
 * <p>
 * {@code -Dspd.fan.verify=true} recomputes every shared result per edge and
 * fails on any difference of contents, iteration order or representation,
 * and prints, at every power of two of the propagations from 2^16 on and at
 * JVM exit, the number of verified results and histograms
 * (powers of two) of the out-degree, the number of distinct type filters
 * and the delta size per propagation.
 */
final class DeltaTransfers {

    private static final boolean VERIFY = Boolean.getBoolean("spd.fan.verify");

    private static final int BUCKETS = Integer.SIZE;

    /**
     * Verify mode prints the statistics at every power of two of the
     * propagations from this one on, and at JVM exit.
     */
    private static final long PRINT_FROM = 1 << 16;

    /**
     * Statistics of verify mode: propagations, transfer applications, type
     * filter results computed, type filter results reused (each verified),
     * differences found.
     */
    private static final AtomicLongArray COUNTS = new AtomicLongArray(5);

    private static final AtomicLongArray OUT_DEGREE = new AtomicLongArray(BUCKETS);

    private static final AtomicLongArray DISTINCT_FILTERS = new AtomicLongArray(BUCKETS);

    private static final AtomicLongArray DELTA_SIZE = new AtomicLongArray(BUCKETS);

    static {
        if (VERIFY) {
            Runtime.getRuntime().addShutdownHook(new Thread(DeltaTransfers::printStatistics));
        }
    }

    /**
     * The type filters applied to the current delta, in {@code [0, size)}.
     */
    private TypeFilter[] applied = new TypeFilter[16];

    private int size;

    private long transfers;

    /**
     * Applies the transfer of the edge to the delta, reusing the result of a
     * type filter already applied to it since the last {@link #finish}.
     *
     * @param edge the edge, or null for an edge stored without an edge
     *             object (its transfer does not read the edge)
     */
    PointsToSet apply(@Nullable PointerFlowEdge edge, Transfer transfer, PointsToSet delta) {
        if (VERIFY) {
            transfers++;
        }
        if (transfer.getClass() != TypeFilter.class) {
            return transfer.apply(edge, delta);
        }
        TypeFilter filter = (TypeFilter) transfer;
        PointsToSet shared = filter.deltaResult;
        if (shared != null && filter.deltaInput == delta) {
            if (VERIFY) {
                verify(filter, edge, delta, shared);
            }
            return shared;
        }
        PointsToSet result = filter.apply(edge, delta);
        if (shared == null) {
            if (size == applied.length) {
                applied = Arrays.copyOf(applied, size * 2);
            }
            applied[size++] = filter;
        }
        filter.deltaInput = delta;
        filter.deltaResult = result;
        return result;
    }

    /**
     * Ends the propagation of the delta from the pointer: forgets the
     * results kept for it.
     */
    void finish(Pointer pointer, PointsToSet delta) {
        if (VERIFY) {
            record(pointer, delta);
        }
        for (int i = 0; i < size; i++) {
            applied[i].deltaInput = null;
            applied[i].deltaResult = null;
            applied[i] = null;
        }
        size = 0;
    }

    private void record(Pointer pointer, PointsToSet delta) {
        long propagations = COUNTS.incrementAndGet(0);
        COUNTS.addAndGet(1, transfers);
        COUNTS.addAndGet(2, size);
        OUT_DEGREE.incrementAndGet(bucket(pointer.getOutDegree()));
        DISTINCT_FILTERS.incrementAndGet(bucket(size));
        DELTA_SIZE.incrementAndGet(bucket(delta.size()));
        transfers = 0;
        if (propagations >= PRINT_FROM && Long.bitCount(propagations) == 1) {
            printStatistics();
        }
    }

    private static void verify(TypeFilter filter, @Nullable PointerFlowEdge edge,
                               PointsToSet delta, PointsToSet shared) {
        PointsToSet expected = filter.apply(edge, delta);
        List<CSObj> want = new ArrayList<>(expected.getObjects());
        List<CSObj> got = new ArrayList<>(shared.getObjects());
        COUNTS.incrementAndGet(3);
        if (!want.equals(got) || expected.getClass() != shared.getClass()
                || TypeFilter.representation(expected) != TypeFilter.representation(shared)) {
            COUNTS.incrementAndGet(4);
            throw new AssertionError("shared type filter result differs on " + edge
                    + ": expected " + want + " (" + TypeFilter.representation(expected)
                    + "), got " + got + " (" + TypeFilter.representation(shared) + ")");
        }
    }

    /**
     * @return the power-of-two bucket of n: 0 for 0, k for [2^(k-1), 2^k).
     */
    private static int bucket(int n) {
        return BUCKETS - Integer.numberOfLeadingZeros(n);
    }

    private static void printStatistics() {
        long filters = COUNTS.get(2) + COUNTS.get(3);
        System.err.println("[spd] fan propagations " + COUNTS.get(0)
                + " transfers " + COUNTS.get(1)
                + " filter results computed " + COUNTS.get(2)
                + " reused and verified " + COUNTS.get(3)
                + " repeat share " + (filters == 0 ? 0 : COUNTS.get(3) * 1000 / filters) + " per mille"
                + " differences " + COUNTS.get(4));
        System.err.println("[spd] fan out-degree " + histogram(OUT_DEGREE));
        System.err.println("[spd] fan distinct filters " + histogram(DISTINCT_FILTERS));
        System.err.println("[spd] fan delta size " + histogram(DELTA_SIZE));
    }

    private static String histogram(AtomicLongArray buckets) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < BUCKETS; i++) {
            long n = buckets.get(i);
            if (n != 0) {
                b.append(i == 0 ? "0" : "<" + (1L << i)).append('=').append(n).append(' ');
            }
        }
        return b.toString().trim();
    }
}
