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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.Set;

import static pascal.taie.analysis.pta.pts.PointsToSetCensus.BUCKETS;
import static pascal.taie.analysis.pta.pts.PointsToSetCensus.bucket;
import static pascal.taie.analysis.pta.pts.PointsToSetCensus.formatHistogram;

/**
 * The measurement counters of {@link LambdaAnalysis}, kept only when the
 * pointer analysis keeps counters; they read and count, and change no
 * result and no order:
 * <ul>
 *     <li>per path, the dispatches of a receiver type group
 *     ({@code enter} of the grouping visitor) and those that found a
 *     callee: {@link #PATH_CALL} at a lambda invocation, {@link #PATH_NEW_PTS}
 *     for a new points-to set of a receiver variable grouped per
 *     invocation, {@link #PATH_SHARED} grouped once per target method;</li>
 *     <li>the points-to updates of a callee's this variable, and those
 *     repeating a callee already updated in the same event (one lambda
 *     invocation or one new points-to set);</li>
 *     <li>the lambda call edges offered to the solver (handed to it, or
 *     found already in the call graph and not built), those handed to it,
 *     and those the call graph took as new;</li>
 *     <li>per edge path ({@link #EDGE_PATH_NAMES}), the offered edges found
 *     already in the call graph (redundant); the calls at a lambda
 *     invocation of a call site and source already registered for the
 *     receiver variable (repeated), and those the option
 *     {@code lambda-skip-repeated-call} skipped; the this updates whose receivers the
 *     this variable already points to (redundant);</li>
 *     <li>at the finish, the receiver variables by their number of
 *     invocation infos, in log2 buckets.</li>
 * </ul>
 */
final class LambdaCounters {

    static final int PATH_CALL = 0;

    static final int PATH_NEW_PTS = 1;

    static final int PATH_SHARED = 2;

    private static final String[] PATH_NAMES = {"call", "new_pts", "shared"};

    private final long[] enters = new long[PATH_NAMES.length];

    private final long[] enterHits = new long[PATH_NAMES.length];

    private long thisUpdates;

    private long repeatedThisUpdates;

    /**
     * The callees whose this variable was updated in the current event.
     */
    private final Set<Callee> eventCallees = new HashSet<>();

    private record Callee(Context context, JMethod method) {
    }

    private long edgesOffered;

    private long edgesHanded;

    private long edgesNew;

    /**
     * The edge path of a single lambda call edge (a constructor or a static
     * method); the grouped paths are {@link #PATH_CALL},
     * {@link #PATH_NEW_PTS} and {@link #PATH_SHARED}.
     */
    static final int EDGE_PATH_SINGLE = 3;

    private static final String[] EDGE_PATH_NAMES = {"call", "new_pts", "shared", "single"};

    private final long[] redundantEdges = new long[EDGE_PATH_NAMES.length];

    private long repeatedSiteSourceCalls;

    private long skippedSiteSourceCalls;

    private long redundantThisUpdates;

    /**
     * Counts an offered lambda call edge on {@code path} that the call graph
     * already holds.
     */
    void edgeRedundant(int path) {
        ++redundantEdges[path];
    }

    /**
     * Counts a call at a lambda invocation whose call site and source the
     * receiver variable already has.
     */
    void repeatedSiteSourceCall() {
        ++repeatedSiteSourceCalls;
    }

    /**
     * Counts a repeated call ({@link #repeatedSiteSourceCall}) that the
     * option {@code lambda-skip-repeated-call} skipped.
     */
    void skippedSiteSourceCall() {
        ++skippedSiteSourceCalls;
    }

    /**
     * Counts a this update whose receivers the this variable already
     * points to.
     */
    void redundantThisUpdate() {
        ++redundantThisUpdates;
    }

    long redundantEdges(int path) {
        return redundantEdges[path];
    }

    long repeatedSiteSourceCalls() {
        return repeatedSiteSourceCalls;
    }

    long skippedSiteSourceCalls() {
        return skippedSiteSourceCalls;
    }

    long redundantThisUpdates() {
        return redundantThisUpdates;
    }

    void enter(int path, boolean hit) {
        ++enters[path];
        if (hit) {
            ++enterHits[path];
        }
    }

    /**
     * Starts an event: the this updates that follow repeat only callees
     * updated after this call.
     */
    void startEvent() {
        eventCallees.clear();
    }

    /**
     * Counts a points-to update of the this variable of {@code callee}
     * under {@code context}; keyed by the pair, so that counting creates no
     * context-sensitive method.
     */
    void thisUpdate(Context context, JMethod callee) {
        ++thisUpdates;
        if (!eventCallees.add(new Callee(context, callee))) {
            ++repeatedThisUpdates;
        }
    }

    /**
     * @return the redundant edges per path, as {@code " edges_redundant_<path>=n"}
     * items.
     */
    private String redundantEdgesText() {
        StringBuilder text = new StringBuilder();
        for (int p = 0; p < EDGE_PATH_NAMES.length; ++p) {
            text.append(" edges_redundant_").append(EDGE_PATH_NAMES[p]).append('=')
                    .append(redundantEdges[p]);
        }
        return text.toString();
    }

    void edgeOffered() {
        ++edgesOffered;
    }

    /**
     * Counts an offered lambda call edge that is built and handed to the
     * solver (not skipped by the prefilter).
     */
    void edgeHanded() {
        ++edgesHanded;
    }

    void edgeNew() {
        ++edgesNew;
    }

    long enters(int path) {
        return enters[path];
    }

    long enterHits(int path) {
        return enterHits[path];
    }

    long thisUpdates() {
        return thisUpdates;
    }

    long repeatedThisUpdates() {
        return repeatedThisUpdates;
    }

    long edgesOffered() {
        return edgesOffered;
    }

    long edgesHanded() {
        return edgesHanded;
    }

    long edgesNew() {
        return edgesNew;
    }

    /**
     * @param infoCounts the number of invocation infos of each receiver
     *                   variable
     * @return the counters in one line, with the histogram of
     * {@code infoCounts}.
     */
    String line(Iterable<Integer> infoCounts) {
        StringBuilder line = new StringBuilder();
        for (int p = 0; p < PATH_NAMES.length; ++p) {
            line.append("enter_").append(PATH_NAMES[p]).append('=').append(enters[p])
                    .append('/').append(enterHits[p]).append(' ');
        }
        long[] histogram = new long[BUCKETS];
        long vars = 0;
        for (int n : infoCounts) {
            ++histogram[bucket(n)];
            ++vars;
        }
        return line.append("this_updates=").append(thisUpdates)
                .append(" this_updates_repeated=").append(repeatedThisUpdates)
                .append(" edges_offered=").append(edgesOffered)
                .append(" edges_new=").append(edgesNew)
                .append(" edges_handed=").append(edgesHanded)
                .append(redundantEdgesText())
                .append(" site_source_calls_repeated=").append(repeatedSiteSourceCalls)
                .append(" site_source_calls_skipped=").append(skippedSiteSourceCalls)
                .append(" this_updates_redundant=").append(redundantThisUpdates)
                .append(" receiver_vars=").append(vars)
                .append(" infos_per_receiver_var=").append(formatHistogram(histogram))
                .toString();
    }
}
