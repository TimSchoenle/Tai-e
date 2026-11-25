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

package pascal.taie.analysis.pta.plugin.exception;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import pascal.taie.analysis.exception.CatchAnalysis;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.callgraph.OtherEdge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.solver.ProgressCounters;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.ConfigException;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.ExceptionEntry;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.Throw;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.IndexerBitSet;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.SetEx;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.IntStream;

public class ExceptionAnalysis implements Plugin {

    private static final Logger logger = LoggerFactory.getLogger(ExceptionAnalysis.class);

    private static final Comparator<CSObj> BY_GLOBAL_INDEX =
            Comparator.comparingInt(CSObj::getIndex);

    private Solver solver;

    private CSManager csManager;

    private TypeSystem typeSystem;

    private ExceptionObjIndexer exceptionIndexer;

    /**
     * Creates the sets of exception objects; every set it creates is over
     * {@link #exceptionIndexer}, so a set from elsewhere (such as a
     * points-to set) enters them element by element.
     */
    private Supplier<SetEx<CSObj>> setFactory;

    /**
     * Receives the exceptions new to a statement or call site, so that a
     * propagation allocates no set for them: they are read only until the
     * propagation that computed them ends (by {@link #handleNew}).
     */
    private SetEx<CSObj> newExceptions;

    /**
     * Whether only application methods are analyzed (option only-app).
     */
    private boolean onlyApp;

    /**
     * The solver's progress counters, which this analysis bumps.
     */
    private ProgressCounters progress;

    /**
     * Map from thrown variables to the corresponding throw statements.
     */
    private MultiMap<Var, Throw> var2Throws = Maps.newMultiMap();

    /**
     * Map from each method with exception entries to the result of catch
     * analysis on it: the entries that may catch what each statement
     * throws, indexed by statement index. Read once per CS method, when
     * its {@link CSMethodThrowResult} is created.
     */
    private Map<JMethod, CSMethodThrowResult.Catchers> catchers = Maps.newMap(1024);

    /**
     * Number of map probes on the propagation path: the explicit-exception
     * probes of throw statements and the catcher probes made when a
     * {@link CSMethodThrowResult} is created.
     */
    long mapProbes;

    /**
     * Number of propagations of a non-empty exception set to a statement.
     */
    long visits;

    /**
     * Number of call edges whose callee's uncaught set was read when the
     * edge was added.
     */
    long callEdgeReads;

    /**
     * Work-list of exception entries to be propagated.
     */
    private ArrayDeque<Work> workList = new ArrayDeque<>();

    /**
     * A drain whose work-list held more items than this replaces the
     * deque afterwards, as an {@link ArrayDeque} never shrinks.
     */
    private static final int TRIM_ABOVE = 1024;

    /**
     * Number of drained entries that brought no exception new to their
     * statement.
     */
    long emptyDiffs;

    /**
     * Largest number of items the work-list held.
     */
    int maxWorkListSize;

    /**
     * A wave over at least this many call edges finds, in parallel and
     * before it hands out its first edge, the callers whose call site
     * already throws all its exceptions (option
     * exception-wave-parallel-threshold).
     */
    private int parallelThreshold;

    /**
     * Number of buckets of {@link #waveStats}: bucket {@code b} holds the
     * waves over {@code [2^(b-1), 2^b)} call edges (bucket 0: no edge).
     */
    private static final int WAVE_BUCKETS = Integer.SIZE;

    /**
     * Per bucket of wave size: the waves, their call edges, and the edges
     * whose caller already threw all the exceptions of the wave.
     */
    final WaveStats waveStats = new WaveStats();

    /**
     * Number of waves whose covered callers were found in parallel, and
     * of the edges they skipped for it.
     */
    long parallelWaves;

    long skippedEdges;

    /**
     * Work counters of the waves, by bucket of wave size.
     */
    static final class WaveStats {

        final long[] waves = new long[WAVE_BUCKETS];

        final long[] edges = new long[WAVE_BUCKETS];

        final long[] emptyDiffs = new long[WAVE_BUCKETS];

        private void record(Wave wave) {
            int bucket = Integer.SIZE - Integer.numberOfLeadingZeros(wave.end);
            waves[bucket]++;
            edges[bucket] += wave.end;
            emptyDiffs[bucket] += wave.emptyDiffs;
        }

        private void clear() {
            Arrays.fill(waves, 0);
            Arrays.fill(edges, 0);
            Arrays.fill(emptyDiffs, 0);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            for (int b = 0; b < WAVE_BUCKETS; b++) {
                if (waves[b] != 0) {
                    sb.append(sb.isEmpty() ? "" : "; ")
                            .append("<").append(1L << b).append(" edges: ")
                            .append(waves[b]).append(" waves, ")
                            .append(edges[b]).append(" edges, ")
                            .append(emptyDiffs[b]).append(" empty");
                }
            }
            return sb.isEmpty() ? "no waves" : sb.toString();
        }
    }

    /**
     * Work-list items.
     */
    private sealed interface Work permits Entry, CallEntry, Wave {
    }

    /**
     * Exceptions that {@code stmt} of {@code csMethod} may throw.
     */
    private record Entry(CSMethod csMethod, Stmt stmt, Set<CSObj> exceptions)
            implements Work {
    }

    /**
     * Exceptions that {@code callSite} may throw.
     */
    private record CallEntry(CSCallSite callSite, Set<CSObj> exceptions)
            implements Work {
    }

    /**
     * Uncaught exceptions of {@code callee} that go out over its call edges
     * {@code next} to {@code end - 1}, one edge at a time, each as an entry
     * at the head of the work-list.
     */
    private static final class Wave implements Work {

        private final CSMethod callee;

        private final Set<CSObj> exceptions;

        private final int end;

        private int next;

        /**
         * Whether the covered callers were looked for.
         */
        private boolean filtered;

        /**
         * The edges whose caller already throws all {@link #exceptions} at
         * the call site, by edge index; null if they were not looked for.
         */
        private boolean[] covered;

        /**
         * Number of edges of this wave that brought nothing new.
         */
        private int emptyDiffs;

        private Wave(CSMethod callee, Set<CSObj> exceptions) {
            this.callee = callee;
            this.exceptions = exceptions;
            this.end = callee.getEdgeCount();
        }

        private boolean isDone() {
            return next >= end;
        }
    }

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        this.csManager = solver.getCSManager();
        this.typeSystem = solver.getTypeSystem();
        // use sparse bit set only when exception objects are NOT merged
        boolean isSparse = !solver.getOptions().getBoolean("merge-exception-objects");
        // number exception objects locally, so that the width of a set
        // follows the number of exception objects, not the global indexes
        this.exceptionIndexer = new ExceptionObjIndexer();
        this.setFactory = () -> new IndexerBitSet<>(exceptionIndexer, isSparse);
        this.newExceptions = setFactory.get();
        this.onlyApp = solver.getOptions().getBoolean("only-app");
        this.progress = solver.getProgressCounters();
        this.emptyDiffs = 0;
        this.maxWorkListSize = 0;
        this.mapProbes = 0;
        this.visits = 0;
        this.callEdgeReads = 0;
        this.parallelThreshold = solver.getOptions()
                .getInt("exception-wave-parallel-threshold");
        if (parallelThreshold < 1) {
            throw new ConfigException("exception-wave-parallel-threshold must be"
                    + " at least 1, got " + parallelThreshold);
        }
        this.waveStats.clear();
        this.parallelWaves = 0;
        this.skippedEdges = 0;
    }

    /**
     * For the throw statements in the method, analyzes and records all the
     * exception entries that handle the exceptions thrown by the statements.
     *
     * @param method the method that the solver meet now
     */
    @Override
    public void onNewMethod(JMethod method) {
        IR ir = method.getIR();
        Map<Stmt, List<ExceptionEntry>> potential = CatchAnalysis.getPotentialCatchers(ir);
        if (!potential.isEmpty()) {
            ExceptionEntry[][] byIndex = new ExceptionEntry[ir.getStmts().size()][];
            potential.forEach((stmt, entries) ->
                    byIndex[stmt.getIndex()] = entries.toArray(new ExceptionEntry[0]));
            catchers.put(method, new CSMethodThrowResult.Catchers(ir.getStmts(), byIndex));
        }
    }

    /**
     * @return the {@link CSMethodThrowResult} of {@code csMethod}, created
     * on the first call.
     */
    private CSMethodThrowResult throwResultOf(CSMethod csMethod) {
        CSMethodThrowResult result = csMethod.getThrowResult();
        if (result == null) {
            ++mapProbes;
            result = new CSMethodThrowResult(setFactory,
                    catchers.get(csMethod.getMethod()));
            csMethod.setThrowResult(result);
        }
        return result;
    }

    /**
     * Establishes the map from all exception references to related throw statements.
     *
     * @param stmt new reachable stmt
     */
    @Override
    public void onNewStmt(Stmt stmt, JMethod container) {
        if (stmt instanceof Throw throwStmt) {
            Var exceptionRef = throwStmt.getExceptionRef();
            var2Throws.put(exceptionRef, throwStmt);
        }
    }

    /**
     * If the csVar is an exception reference, propagate all the exception
     * it newly throws.
     *
     * @param csVar variable pointer
     * @param pts   objects added to the csVar points to set
     */
    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        Set<Throw> throwStmts = var2Throws.get(csVar.getVar());
        if (!throwStmts.isEmpty()) {
            Var exceptionRef = csVar.getVar();
            Context ctx = csVar.getContext();
            JMethod currentMethod = exceptionRef.getMethod();
            CSMethod currentCSMethod = csManager.getCSMethod(ctx, currentMethod);
            // copy element by element: pts is numbered by the global indexer
            SetEx<CSObj> thrown = setFactory.get();
            for (CSObj obj : pts) {
                thrown.add(obj);
            }
            throwStmts.forEach(throwStmt -> workList.add(
                    new Entry(currentCSMethod, throwStmt, thrown)));
            propagateExceptions();
        }
    }

    /**
     * For a new call edge, the exception thrown by the callee method should be
     * propagated to its callers, and thrown by the invoke statement,
     * then we propagate the thrown exceptions accordingly.
     *
     * @param edge the newly established call edge
     */
    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (propagatesExceptions(edge)) {
            CSMethodThrowResult csResult = edge.getCallee().getThrowResult();
            if (csResult != null) {
                ++callEdgeReads;
                // the live set, as the unmodifiable view passed before:
                // it is only read, and the work-list is empty, so this
                // entry is drained first, before addUncaughtExceptions
                // can grow the set
                Set<CSObj> exceptions = csResult.uncaughtSet();
                if (!exceptions.isEmpty()) {
                    workList.add(new CallEntry(edge.getCallSite(), exceptions));
                    propagateExceptions();
                }
            }
        }
    }

    /**
     * Propagates exceptions from callees to callers (and callers' caller).
     * When a statement throws new exceptions, call {@link #analyzeIntraUncaught}
     * to handle the exceptions that can be caught by the containing method.
     * If there are uncaught exceptions in the method, they will be propagated
     * to call site (invoke) of the method.
     */
    private void propagateExceptions() {
        int peak = 0;
        while (!workList.isEmpty()) {
            peak = Math.max(peak, workList.size());
            progress.drainEntry(workList.size());
            Work head = workList.peek();
            if (head instanceof Wave wave) {
                // the wave stays at the head until its last edge is taken,
                // so its entries drain where the entries queued per edge
                // used to: the edges do not change during a drain
                if (!wave.filtered) {
                    wave.filtered = true;
                    if (wave.end >= parallelThreshold) {
                        findCovered(wave);
                    }
                }
                Edge<CSCallSite, CSMethod> edge = takeEdge(wave);
                boolean done = wave.isDone();
                if (done) {
                    workList.poll();
                }
                if (edge != null) {
                    progress.visitEdge();
                    if (propagate(edge.getCallSite(), wave.exceptions)) {
                        wave.emptyDiffs++;
                    }
                }
                if (done) {
                    waveStats.record(wave);
                }
            } else if (head instanceof CallEntry callEntry) {
                workList.poll();
                propagate(callEntry.callSite(), callEntry.exceptions());
            } else {
                workList.poll();
                Entry entry = (Entry) head;
                propagate(entry.csMethod(), entry.stmt(), entry.exceptions());
            }
        }
        progress.setPendingEntries(0);
        maxWorkListSize = Math.max(maxWorkListSize, peak);
        if (peak > TRIM_ABOVE) {
            workList = new ArrayDeque<>();
        }
    }

    /**
     * @return the next edge of {@code wave} that propagates exceptions and
     * whose caller was not found covered, or null if no such edge is left.
     * Each edge found covered counts as an entry that brought nothing new.
     */
    private Edge<CSCallSite, CSMethod> takeEdge(Wave wave) {
        boolean[] covered = wave.covered;
        while (wave.next < wave.end) {
            int index = wave.next++;
            if (covered != null && covered[index]) {
                // the counters the sequential visit of this edge would
                // have moved (visitEdge, skips, handleNew's empty diff)
                progress.visitEdge();
                ++visits;
                emptyDiffs++;
                progress.addEmptyDiff();
                wave.emptyDiffs++;
                skippedEdges++;
                if (wave.next < wave.end) {
                    // sequentially the rest of the wave is taken in the
                    // next loop iteration of propagateExceptions, which
                    // drains one entry (and may run the progress check)
                    progress.drainEntry(workList.size());
                }
                continue;
            }
            Edge<CSCallSite, CSMethod> edge = wave.callee.getEdge(index);
            if (propagatesExceptions(edge)) {
                return edge;
            }
        }
        return null;
    }

    /**
     * Finds, in parallel, the edges of {@code wave} whose caller already
     * throws all exceptions of the wave at the call site. Nothing adds to
     * the call sites' thrown sets while the tasks run. A dense set only reads in
     * containsAll; a sparse set may drop its all-zero blocks there, which
     * changes no element. Two edges of one call site (a regular and an
     * other edge into the same callee) can make two tasks check one set;
     * a dropped block is zero either way, so each answer is the one a
     * single thread gives. The sets only grow while the wave drains, so an
     * edge found covered stays covered until it is taken, and taking it
     * would bring nothing new.
     */
    private void findCovered(Wave wave) {
        boolean[] covered = new boolean[wave.end];
        CSMethod callee = wave.callee;
        Set<CSObj> exceptions = wave.exceptions;
        IntStream.range(0, covered.length).parallel().forEach(i ->
                covered[i] = isCovered(callee.getEdge(i), exceptions));
        wave.covered = covered;
        parallelWaves++;
    }

    /**
     * @return whether {@link #propagate} over {@code edge} would count the
     * exceptions as bringing nothing new; reads only.
     */
    private boolean isCovered(Edge<CSCallSite, CSMethod> edge, Set<CSObj> exceptions) {
        if (!propagatesExceptions(edge) || exceptions.isEmpty()) {
            return false;
        }
        CSCallSite callSite = edge.getCallSite();
        CSMethod caller = callSite.getContainer();
        if (onlyApp && !caller.getMethod().isApplication()) {
            return false;
        }
        return CSMethodThrowResult.throwsAll(callSite, exceptions);
    }

    /**
     * Adds the exceptions to those that {@code stmt} of {@code csMethod} may
     * throw, and queues a wave of those that the method newly does not catch.
     */
    private void propagate(CSMethod csMethod, Stmt stmt, Set<CSObj> exceptions) {
        if (skips(csMethod, exceptions)) {
            return;
        }
        CSMethodThrowResult result = throwResultOf(csMethod);
        ++mapProbes;
        handleNew(csMethod, result, stmt,
                result.propagate(stmt, exceptions, newExceptions));
    }

    /**
     * Adds the exceptions to those that {@code callSite} may throw, and
     * queues a wave of those that its container newly does not catch.
     *
     * @return whether the exceptions brought nothing new to {@code callSite}
     * (false when the propagation was skipped).
     */
    private boolean propagate(CSCallSite callSite, Set<CSObj> exceptions) {
        CSMethod csMethod = callSite.getContainer();
        if (skips(csMethod, exceptions)) {
            return false;
        }
        CSMethodThrowResult result = throwResultOf(csMethod);
        return handleNew(csMethod, result, callSite.getCallSite(),
                result.propagate(callSite, exceptions, newExceptions));
    }

    /**
     * @return whether a propagation of {@code exceptions} into
     * {@code csMethod} does nothing; otherwise counts it as a visit.
     */
    private boolean skips(CSMethod csMethod, Set<CSObj> exceptions) {
        // Temporary fix: skip non-application methods when only-app is enabled.
        if (onlyApp && !csMethod.getMethod().isApplication()) {
            return true;
        }
        if (exceptions.isEmpty()) {
            return true;
        }
        ++visits;
        return false;
    }

    /**
     * Passes the exceptions {@code diff} new to {@code stmt} of
     * {@code csMethod} to its handlers, and queues a wave of those that the
     * method newly does not catch.
     *
     * @return whether {@code diff} is empty (nothing new to {@code stmt}).
     */
    private boolean handleNew(CSMethod csMethod, CSMethodThrowResult result,
                              Stmt stmt, Set<CSObj> diff) {
        if (diff.isEmpty()) {
            emptyDiffs++;
            progress.addEmptyDiff();
            return true;
        }
        Set<CSObj> uncaught = analyzeIntraUncaught(stmt, diff, csMethod, result);
        // only the exceptions new to the uncaught set go out: every
        // other one went out over each edge into csMethod when it
        // entered the set, or with the whole set when the edge was
        // added (onNewCallEdge), and those entries drained first
        Set<CSObj> fresh = uncaught.isEmpty()
                ? uncaught
                : result.addUncaughtExceptions(uncaught);
        if (!fresh.isEmpty() && csMethod.getEdgeCount() > 0) {
            workList.add(new Wave(csMethod, fresh));
            progress.addWave();
        }
        return false;
    }

    /**
     * @return whether the exceptions that the callee of {@code edge} does not
     * catch leave its call site: true for regular calls and for the
     * {@link CallKind#OTHER} edges whose call site calls the callee.
     */
    private static boolean propagatesExceptions(Edge<CSCallSite, CSMethod> edge) {
        return edge.getKind() != CallKind.OTHER
                || (edge instanceof OtherEdge<?, ?> otherEdge
                && otherEdge.propagatesExceptions());
    }

    /**
     * Performs an intra-procedural analysis to compute the exceptions that are
     * not caught by the current method.
     *
     * @param currentStmt   the statements that throws exceptions
     * @param newExceptions the new-found exceptions thrown by currentStmt
     * @param csMethod      the csMethod containing currentStmt
     * @param result        the throw result of csMethod
     * @return the exceptions thrown by currentStmt but not caught by
     * csMethod: {@code newExceptions} itself when no handler catches any
     */
    private Set<CSObj> analyzeIntraUncaught(
            Stmt currentStmt,
            Set<CSObj> newExceptions,
            CSMethod csMethod,
            CSMethodThrowResult result) {
        ExceptionEntry[] entries = result.catchersOf(currentStmt);
        if (entries == null) {
            return newExceptions;
        }
        Context ctx = csMethod.getContext();
        // the exceptions still uncaught, in global index order, kept in
        // place: each handler keeps a prefix of what the previous one kept
        CSObj[] toCheck = inGlobalIndexOrder(newExceptions);
        int size = toCheck.length;
        for (ExceptionEntry entry : entries) {
            Type catchType = entry.catchType();
            Var exceptionRef = entry.handler().getExceptionRef();
            Type lastType = null;
            boolean lastCaught = false;
            int kept = 0;
            for (int i = 0; i < size; ++i) {
                CSObj newException = toCheck[i];
                Type type = newException.getObject().getType();
                if (type != lastType) {
                    lastType = type;
                    lastCaught = typeSystem.isSubtype(catchType, type);
                }
                if (lastCaught) {
                    solver.addVarPointsTo(ctx, exceptionRef, newException);
                } else {
                    toCheck[kept++] = newException;
                }
            }
            size = kept;
        }
        if (size == toCheck.length) {
            return newExceptions;
        }
        SetEx<CSObj> uncaughtExceptions = setFactory.get();
        for (int i = 0; i < size; ++i) {
            uncaughtExceptions.add(toCheck[i]);
        }
        return uncaughtExceptions;
    }

    /**
     * @return the given objects in the order of their global indexes, the
     * iteration order of sets over the global {@link CSObj} indexer, so the
     * solver receives caught objects in the same order whichever indexer
     * numbers the exception sets; a new array the caller may change.
     */
    private static CSObj[] inGlobalIndexOrder(Set<CSObj> objs) {
        CSObj[] sorted = objs.toArray(new CSObj[0]);
        if (sorted.length > 1) {
            Arrays.sort(sorted, BY_GLOBAL_INDEX);
        }
        return sorted;
    }

    @Override
    public void onFinish() {
        logCensus();
        if (!solver.getOptions().getBoolean("collect-throw-results")) {
            clear();
            return;
        }
        // Collects context-sensitive throw results and stores them in
        // a context-insensitive manner.
        PTAThrowResult throwResult = new PTAThrowResult();
        for (CSMethod csMethod : solver.getCallGraph()) {
            JMethod method = csMethod.getMethod();
            MethodThrowResult result = throwResult.getOrCreateResult(method);
            CSMethodThrowResult csResult = csMethod.getThrowResult();
            if (csResult != null) {
                result.addCSMethodThrowResult(csResult);
            }
        }
        solver.getResult().storeResult(getClass().getName(), throwResult);
        clear();
    }

    /**
     * Logs the work counters, then one line: how many exception objects
     * got a local index and, for a {@link MapBasedCSManager}, how many
     * throwable objects got a global
     * index and whether and when they ran out of their reserved range.
     */
    private void logCensus() {
        logger.info("Exception work: {} entries brought nothing new;"
                + " work-list peak {} items", emptyDiffs, maxWorkListSize);
        logger.info("Exception waves: {}; {} waves filtered in parallel,"
                + " {} covered edges skipped", waveStats, parallelWaves, skippedEdges);
        if (csManager instanceof MapBasedCSManager mapBased) {
            MapBasedCSManager.ThrowableCensus census = mapBased.getThrowableCensus();
            logger.info("Exception objects: {} indexed by exception analysis;"
                            + " throwable objects: {} (reserved indexes {}, {})",
                    exceptionIndexer.size(), census.throwableObjects(), census.budget(),
                    census.budgetExceeded()
                            ? "exceeded after " + census.budgetExceededAfterMillis() + " ms"
                            : "not exceeded");
        } else {
            logger.info("Exception objects: {} indexed by exception analysis",
                    exceptionIndexer.size());
        }
    }

    private void clear() {
        var2Throws = null;
        catchers = null;
        workList = null;
        newExceptions = null;
    }
}
