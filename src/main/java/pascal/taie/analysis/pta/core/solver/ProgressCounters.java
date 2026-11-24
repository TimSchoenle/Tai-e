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

/**
 * Progress counters that plugins running on the solver thread may bump
 * (for example the exception analysis: its pending entries and waves).
 * The solver's progress line reports them when they are non-zero.
 * The counters are plain fields: they are written and read only on the
 * solver thread.
 */
public final class ProgressCounters {

    private static final Runnable NO_CHECK = () -> {
    };

    private long pendingEntries;

    private long waves;

    private long entriesDrained;

    private long edgesVisited;

    private long emptyDiffs;

    /**
     * Runs the solver's progress check; a no-op for solvers without a
     * progress line.
     */
    private Runnable progressCheck = NO_CHECK;

    /**
     * {@link #progressCheck} runs when the drained-entry count has none of
     * these bits set.
     */
    private long checkMask = -1;

    /**
     * Sets the number of entries a plugin currently holds pending.
     */
    public void setPendingEntries(long pendingEntries) {
        this.pendingEntries = pendingEntries;
    }

    /**
     * Counts one more wave of a plugin.
     */
    public void addWave() {
        ++waves;
    }

    /**
     * Counts one entry a plugin drained from its own work list, with
     * {@code pending} entries left; at the solver's check mask it also
     * records {@code pending} and runs the solver's progress check, so a
     * long plugin drain still logs progress lines.
     */
    public void drainEntry(long pending) {
        if ((++entriesDrained & checkMask) == 0) {
            pendingEntries = pending;
            progressCheck.run();
        }
    }

    /**
     * Counts one call edge a plugin visited.
     */
    public void visitEdge() {
        ++edgesVisited;
    }

    /**
     * Counts one drained entry that brought nothing new.
     */
    public void addEmptyDiff() {
        ++emptyDiffs;
    }

    /**
     * Installs the solver's progress check, run by {@link #drainEntry(long)}
     * when the drained-entry count has none of the bits of
     * {@code checkMask} set.
     */
    void setProgressCheck(Runnable progressCheck, long checkMask) {
        this.progressCheck = progressCheck;
        this.checkMask = checkMask;
    }

    /**
     * Clears the counters; the solver calls it when a solve starts.
     */
    void reset() {
        pendingEntries = 0;
        waves = 0;
        entriesDrained = 0;
        edgesVisited = 0;
        emptyDiffs = 0;
    }

    public long getEntriesDrained() {
        return entriesDrained;
    }

    public long getEdgesVisited() {
        return edgesVisited;
    }

    public long getEmptyDiffs() {
        return emptyDiffs;
    }

    public long getPendingEntries() {
        return pendingEntries;
    }

    public long getWaves() {
        return waves;
    }
}
