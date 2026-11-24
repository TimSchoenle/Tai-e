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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.ExceptionEntry;
import pascal.taie.ir.stmt.Catch;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.Throw;
import pascal.taie.language.classes.JMethod;
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
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

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
     * Whether only application methods are analyzed (option only-app).
     */
    private boolean onlyApp;

    /**
     * The key of the {@link CSMethodThrowResult} of each CS method.
     */
    private String resultKey;

    /**
     * Creates the {@link CSMethodThrowResult} of a CS method.
     */
    private Supplier<CSMethodThrowResult> resultFactory;

    /**
     * Map from thrown variables to the corresponding throw statements.
     */
    private MultiMap<Var, Throw> var2Throws = Maps.newMultiMap();

    /**
     * Map from each method to the result of catch analysis on it.
     */
    private Map<JMethod, Map<Stmt, List<ExceptionEntry>>> catchers =
            Maps.newMap(1024);

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
     * Work-list items.
     */
    private sealed interface Work permits Entry, Wave {
    }

    /**
     * Exceptions that {@code stmt} of {@code csMethod} may throw.
     */
    private record Entry(CSMethod csMethod, Stmt stmt, Set<CSObj> exceptions)
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

        private Wave(CSMethod callee, Set<CSObj> exceptions) {
            this.callee = callee;
            this.exceptions = exceptions;
            this.end = callee.getEdgeCount();
        }

        /**
         * @return the next edge that propagates exceptions, or null if no
         * such edge is left.
         */
        private Edge<CSCallSite, CSMethod> takeEdge() {
            while (next < end) {
                Edge<CSCallSite, CSMethod> edge = callee.getEdge(next++);
                if (propagatesExceptions(edge)) {
                    return edge;
                }
            }
            return null;
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
        this.onlyApp = solver.getOptions().getBoolean("only-app");
        this.resultKey = getClass().getName();
        this.resultFactory = () -> new CSMethodThrowResult(setFactory);
        this.emptyDiffs = 0;
        this.maxWorkListSize = 0;
    }

    /**
     * For the throw statements in the method, analyzes and records all the
     * exception entries that handle the exceptions thrown by the statements.
     *
     * @param method the method that the solver meet now
     */
    @Override
    public void onNewMethod(JMethod method) {
        catchers.put(method,
                CatchAnalysis.getPotentialCatchers(method.getIR()));
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
            CSMethod callee = edge.getCallee();
            Optional<CSMethodThrowResult> csResult = callee.getResult(resultKey);
            if (csResult.isPresent()) {
                // the live set, as the unmodifiable view passed before:
                // it is only read, and the work-list is empty, so this
                // entry is drained first, before addUncaughtExceptions
                // can grow the set
                Set<CSObj> exceptions = csResult.get().uncaughtSet();
                if (!exceptions.isEmpty()) {
                    CSMethod caller = edge.getCallSite().getContainer();
                    Invoke invoke = edge.getCallSite().getCallSite();
                    workList.add(new Entry(caller, invoke, exceptions));
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
            Work head = workList.peek();
            if (head instanceof Wave wave) {
                // the wave stays at the head until its last edge is taken,
                // so its entries drain where the entries queued per edge
                // used to: the edges do not change during a drain
                Edge<CSCallSite, CSMethod> edge = wave.takeEdge();
                if (wave.isDone()) {
                    workList.poll();
                }
                if (edge != null) {
                    CSCallSite callSite = edge.getCallSite();
                    propagate(callSite.getContainer(), callSite.getCallSite(),
                            wave.exceptions);
                }
            } else {
                workList.poll();
                Entry entry = (Entry) head;
                propagate(entry.csMethod(), entry.stmt(), entry.exceptions());
            }
        }
        maxWorkListSize = Math.max(maxWorkListSize, peak);
        if (peak > TRIM_ABOVE) {
            workList = new ArrayDeque<>();
        }
    }

    /**
     * Adds the exceptions to those that {@code stmt} of {@code csMethod} may
     * throw, and queues a wave of those that the method newly does not catch.
     */
    private void propagate(CSMethod csMethod, Stmt stmt, Set<CSObj> exceptions) {
        // Temporary fix: skip non-application methods when only-app is enabled.
        if (onlyApp && !csMethod.getMethod().isApplication()) {
            return;
        }
        if (exceptions.isEmpty()) {
            return;
        }
        CSMethodThrowResult result = csMethod.getResult(resultKey, resultFactory);
        Set<CSObj> diff = result.propagate(stmt, exceptions);
        if (diff.isEmpty()) {
            emptyDiffs++;
            return;
        }
        Set<CSObj> uncaught = analyzeIntraUncaught(stmt, diff, csMethod);
        // only the exceptions new to the uncaught set go out: every
        // other one went out over each edge into csMethod when it
        // entered the set, or with the whole set when the edge was
        // added (onNewCallEdge), and those entries drained first
        Set<CSObj> fresh = uncaught.isEmpty()
                ? uncaught
                : result.addUncaughtExceptions(uncaught);
        if (!fresh.isEmpty() && csMethod.getEdgeCount() > 0) {
            workList.add(new Wave(csMethod, fresh));
        }
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
     * @return the exceptions thrown by currentStmt but not caught by csMethod
     */
    private Set<CSObj> analyzeIntraUncaught(
            Stmt currentStmt,
            Set<CSObj> newExceptions,
            CSMethod csMethod) {
        List<ExceptionEntry> entries = catchers.getOrDefault(csMethod.getMethod(), Map.of())
                .get(currentStmt);
        if (entries != null) {
            Context ctx = csMethod.getContext();
            Iterable<CSObj> toCheck = inGlobalIndexOrder(newExceptions);
            for (ExceptionEntry entry : entries) {
                SetEx<CSObj> uncaughtExceptions = setFactory.get();
                for (CSObj newException : toCheck) {
                    Obj exObj = newException.getObject();
                    if (typeSystem.isSubtype(entry.catchType(), exObj.getType())) {
                        Catch catchStmt = entry.handler();
                        Var exceptionRef = catchStmt.getExceptionRef();
                        solver.addVarPointsTo(ctx, exceptionRef, newException);
                    } else {
                        uncaughtExceptions.add(newException);
                    }
                }
                newExceptions = uncaughtExceptions;
                toCheck = inGlobalIndexOrder(uncaughtExceptions);
            }
        }
        return newExceptions;
    }

    /**
     * @return the given objects in the order of their global indexes, the
     * iteration order of sets over the global {@link CSObj} indexer, so the
     * solver receives caught objects in the same order whichever indexer
     * numbers the exception sets.
     */
    private static Iterable<CSObj> inGlobalIndexOrder(Set<CSObj> objs) {
        if (objs.size() < 2) {
            return objs;
        }
        CSObj[] sorted = objs.toArray(new CSObj[0]);
        Arrays.sort(sorted, BY_GLOBAL_INDEX);
        return Arrays.asList(sorted);
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
            Optional<CSMethodThrowResult> csResult =
                    csMethod.getResult(getClass().getName());
            csResult.ifPresent(result::addCSMethodThrowResult);
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
    }
}
