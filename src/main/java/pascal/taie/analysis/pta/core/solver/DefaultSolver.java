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
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.exception.CSMethodThrowResult;
import pascal.taie.analysis.pta.pts.HeapOwnerCensus;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.analysis.pta.pts.PointsToSetInterner;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.config.ConfigException;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.Literal;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.NewMultiArray;
import pascal.taie.ir.exp.PhiExp;
import pascal.taie.ir.exp.ReferenceLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.AssignLiteral;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Phi;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

import static pascal.taie.language.classes.Signatures.FINALIZE;
import static pascal.taie.language.classes.Signatures.FINALIZER_REGISTER;

public class DefaultSolver implements Solver {

    private static final Logger logger = LoggerFactory.getLogger(DefaultSolver.class);

    /**
     * Descriptor for array objects created implicitly by multiarray instruction.
     */
    private static final Descriptor MULTI_ARRAY_DESC = () -> "MultiArrayObj";

    /**
     * Number that represents unlimited elapsed time.
     */
    private static final long UNLIMITED = -1;

    /**
     * Mask of the work list iterations at which the progress clock is read:
     * every 8192 iterations.
     */
    private static final long PROGRESS_CHECK_MASK = (1L << 13) - 1;

    private static final long NANOS_PER_SECOND = 1_000_000_000L;

    private static final long NANOS_PER_MS = 1_000_000L;

    private static final long BYTES_PER_MB = 1L << 20;

    private static final String PROGRESS_FORMAT = "PTA progress: elapsed_s={}"
            + " iterations={} pending_pointers={} pending_call_edges={}"
            + " cs_methods={} methods={} cs_call_edges={} pointers={}"
            + " heap_used_mb={}";

    private static final String PROGRESS_EXT_FORMAT = PROGRESS_FORMAT
            + " ext_pending={} ext_waves={} ext_drained={} ext_edges={}"
            + " ext_empty_diffs={}";

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private final CSManager csManager;

    private final ClassHierarchy hierarchy;

    private final TypeSystem typeSystem;

    private final PointsToSetFactory ptsFactory;

    /**
     * Shares equal points-to sets between pointers; null unless the option
     * {@code share-points-to-sets} is true.
     */
    @Nullable
    private final PointsToSetInterner interner;

    /**
     * With {@link #interner} and the option {@code pack-cold-sets} above 0:
     * the window over the pointers whose shared sets, held by them alone,
     * were changed last; a set that leaves it without a later change is
     * packed between two polls. Null otherwise, and after
     * {@link #releaseSolverState()}.
     */
    @Nullable
    private ColdSetQueue coldSoleSets;

    @Nullable
    private Consumer<Pointer> packColdSole;

    private final PropagateTypes propTypes;

    /**
     * One type filter per guard type: edges with the same guard type share
     * the filter (a filter's behavior depends only on its type and this
     * solver).
     */
    private final Map<Type, TypeFilter> typeFilters = Maps.newMap();

    /**
     * Applies the transfers of out-edges to a propagated delta, each type
     * filter once per delta.
     */
    private final DeltaTransfers deltaTransfers = new DeltaTransfers();

    /**
     * Whether only analyzes application code.
     */
    private final boolean onlyApp;

    /**
     * Whether a call to a trivial getter is taken as a load at the call site
     * (option {@code trivial-getters}, px/s115-P57), see {@link #inlinesGetter}.
     */
    private final boolean trivialGetters;

    /**
     * The trivial getter shape of each resolved callee, made on first use.
     */
    private final Map<JMethod, TrivialGetter> getterShapes = Maps.newMap();

    /**
     * Time limit for pointer analysis (in seconds).
     */
    private final long timeLimit;

    private TimeLimiter timeLimiter;

    /**
     * Interval between progress lines in nanoseconds; 0 means off
     * (option {@code progress-interval}, in seconds). Not final only for
     * {@link #setProgressCheckForTesting(long, long)}.
     */
    private long progressIntervalNanos;

    /**
     * Mask of the work list iterations at which the progress clock is read;
     * {@link #PROGRESS_CHECK_MASK} except in tests.
     */
    private long progressCheckMask = PROGRESS_CHECK_MASK;

    private final ProgressCounters progressCounters = new ProgressCounters();

    /**
     * The block-sharing probe (option {@code call-block-probe}), null when
     * off; it only counts.
     */
    private @Nullable CallBlockProbe blockProbe;

    /**
     * Work list entries processed by the current solve.
     */
    private long iterations;

    /**
     * Context-sensitive call edges added to the call graph by the current
     * solve; kept because counting the graph's edges is not O(1).
     */
    private long csCallEdges;

    private long progressLines;

    private long solveStartNanos;

    private long lastProgressNanos;

    /**
     * Whether the analysis has reached time limit.
     */
    private volatile boolean isTimeout;

    /**
     * Whether the last analysis stopped at its time limit with work left.
     */
    private boolean stoppedByTimeLimit;

    private Plugin plugin;

    private WorkList workList;

    /**
     * Whether {@link #releaseSolverState()} ran: from then on the solver
     * refuses new work (points-to entries, call edges, pointer flow edges),
     * which it would never process.
     */
    private boolean solverStateReleased;

    /**
     * The census taken at the finish with the option {@code census}, or
     * null if the option is off.
     */
    private @Nullable SolverCensus census;

    /**
     * The heap owner census taken with {@link #census}, or null.
     */
    private @Nullable HeapOwnerCensus owners;

    /**
     * When a census is taken during the solve (see {@link LiveCensusClock}).
     */
    private LiveCensusClock liveCensusClock;

    /**
     * The censuses taken during the last solve, and the last of them, or
     * null if none was taken.
     */
    private long liveCensuses;

    /**
     * The time the censuses during the last solve took, reported apart
     * from the solve (a time limit still counts it).
     */
    private long liveCensusNanos;

    private @Nullable SolverCensus lastLiveCensus;

    private @Nullable HeapOwnerCensus lastLiveOwners;

    /**
     * Whether the measurement counters of the solver, its work list, its
     * interner and the type filters are kept and logged (with the option
     * {@code census} or the system property {@value #COUNTERS_PROPERTY});
     * they change no result and no order.
     */
    private final boolean counting;

    static final String COUNTERS_PROPERTY = "taie.pta.counters";

    /**
     * The guards listed in the type filter block at the finish (see
     * {@link TypeFilter#guardsBlock}).
     */
    private static final int GUARD_LINES = 20;

    /**
     * @return whether the measurement counters are kept for a pointer
     * analysis with these options: with the option {@code census} or the
     * system property {@value #COUNTERS_PROPERTY}. Plugins that keep
     * counters of their own ask this too.
     */
    public static boolean countersEnabled(AnalysisOptions options) {
        return options.getBoolean("census") || Boolean.getBoolean(COUNTERS_PROPERTY);
    }

    /**
     * The origins of new points-to work that the counters tell apart, an
     * index into {@link #addsByOrigin}: the initial flow of a new pointer
     * flow edge, the fan-out of a propagation, the receiver objects of
     * {@link #processCall}, and everything else (statements, plugins).
     */
    static final int ORIGIN_OTHER = 0;

    static final int ORIGIN_INITIAL_FLOW = 1;

    static final int ORIGIN_FAN_OUT = 2;

    static final int ORIGIN_PROCESS_CALL = 3;

    private static final String[] ORIGIN_NAMES = {
            "other", "initial_flow", "fan_out", "process_call"};

    /**
     * The origin of the points-to work being added; kept only with
     * {@link #counting}.
     */
    private int addOrigin = ORIGIN_OTHER;

    private final long[] addsByOrigin = new long[ORIGIN_NAMES.length];

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private Set<JMethod> reachableMethods;

    /**
     * Set of classes that have been initialized.
     */
    private Set<JClass> initializedClasses;

    /**
     * Set of methods to be intercepted and ignored.
     */
    private Set<JMethod> ignoredMethods;

    private StmtProcessor stmtProcessor;

    private PointerAnalysisResult result;

    @SuppressWarnings("unchecked")
    public DefaultSolver(AnalysisOptions options, HeapModel heapModel,
                         ContextSelector contextSelector, CSManager csManager) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.csManager = csManager;
        hierarchy = World.get().getClassHierarchy();
        typeSystem = World.get().getTypeSystem();
        ptsFactory = new PointsToSetFactory(csManager.getObjectIndexer());
        int coldWindow = options.getInt("pack-cold-sets");
        if (coldWindow < 0) {
            throw new IllegalArgumentException(
                    "pack-cold-sets must not be negative: " + coldWindow);
        }
        interner = options.getBoolean("share-points-to-sets")
                ? new PointsToSetInterner(ptsFactory, coldWindow > 0) : null;
        counting = countersEnabled(options);
        if (counting && interner != null) {
            interner.enableFormCounters();
        }
        if (interner != null && coldWindow > 0) {
            coldSoleSets = new ColdSetQueue(coldWindow);
            packColdSole = interner::packSoleHeld;
        } else {
            coldSoleSets = null;
            packColdSole = null;
        }
        propTypes = new PropagateTypes(
                (List<String>) options.get("propagate-types"),
                typeSystem);
        onlyApp = options.getBoolean("only-app");
        trivialGetters = options.getBoolean("trivial-getters");
        if (trivialGetters && World.get().getOptions().isAndroidMode()) {
            // the Android models read loads in a callee's body against its
            // own this variable (OtherMiscModel), which a getter taken as a
            // load leaves empty
            throw new ConfigException("trivial-getters is refused in Android mode");
        }
        String advanced = options.getString("advanced");
        if (trivialGetters && advanced != null && !advanced.equals("collection")) {
            // the pre-analyses of Zipper, Scaler and Mahjong read the methods
            // invoked on a type and their flows from the callees' this
            // variables, which a getter taken as a load leaves empty
            throw new ConfigException("trivial-getters is refused with advanced: " + advanced);
        }
        if (trivialGetters && (options.getString("taint-config") != null
                || !((List<?>) options.get("taint-config-providers")).isEmpty())) {
            // a taint sanitizer of a getter's base filters its this variable,
            // which the load at the call site does not pass through
            throw new ConfigException("trivial-getters is refused with taint analysis");
        }
        timeLimit = options.getInt("time-limit");
        int progressInterval = options.getInt("progress-interval");
        if (progressInterval < 0) {
            throw new IllegalArgumentException(
                    "progress-interval must be >= 0, given: " + progressInterval);
        }
        progressIntervalNanos = progressInterval * NANOS_PER_SECOND;
        progressCounters.setProgressCheck(this::checkProgressIfOn, progressCheckMask);
    }

    @Override
    public AnalysisOptions getOptions() {
        return options;
    }

    @Override
    public HeapModel getHeapModel() {
        return heapModel;
    }

    @Override
    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    @Override
    public CSManager getCSManager() {
        return csManager;
    }

    @Override
    public ClassHierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    @Override
    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    @Override
    public ProgressCounters getProgressCounters() {
        return progressCounters;
    }

    @Override
    public @Nullable CallBlockProbe getCallBlockProbe() {
        return blockProbe;
    }

    /**
     * @return the work list entries processed by the last solve.
     */
    public long getIterations() {
        return iterations;
    }

    /**
     * @return the context-sensitive call edges the last solve added.
     */
    public long getNumberOfCSCallEdges() {
        return csCallEdges;
    }

    /**
     * @return the progress lines the last solve logged.
     */
    public long getProgressLines() {
        return progressLines;
    }

    /**
     * Replaces the progress check for tests, whose programs are far smaller
     * than one check period: the clock is read when the work list
     * iteration count has none of the bits of {@code checkMask} set, and a
     * line is logged when {@code intervalNanos} (0 means off) has passed.
     */
    void setProgressCheckForTesting(long checkMask, long intervalNanos) {
        if (checkMask < 0 || intervalNanos < 0) {
            throw new IllegalArgumentException("checkMask and intervalNanos"
                    + " must be >= 0, given: " + checkMask + ", " + intervalNanos);
        }
        progressCheckMask = checkMask;
        progressIntervalNanos = intervalNanos;
        progressCounters.setProgressCheck(this::checkProgressIfOn, checkMask);
    }

    @Override
    public PointsToSet getPointsToSetOf(Pointer pointer) {
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = interner != null ? interner.holdEmpty() : ptsFactory.make();
            pointer.setPointsToSet(pts);
        }
        return pts;
    }

    @Override
    public PointsToSet unsharePointsToSetOf(Pointer pointer) {
        PointsToSet pts = getPointsToSetOf(pointer);
        return interner != null ? interner.unshare(pointer) : pts;
    }

    @Override
    public PointsToSet makePointsToSet() {
        return ptsFactory.make();
    }

    @Override
    public void setPlugin(Plugin plugin) {
        this.plugin = plugin;
    }

    // ---------- solver logic starts ----------

    /**
     * Runs pointer analysis algorithm.
     */
    @Override
    public void solve() {
        initialize();
        analyze();
    }

    @Override
    public boolean isStoppedByTimeLimit() {
        return stoppedByTimeLimit;
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph(csManager);
        workList = newWorkList();
        solverStateReleased = false;
        reachableMethods = Sets.newSet();
        initializedClasses = Sets.newSet();
        ignoredMethods = Sets.newSet();
        stmtProcessor = new StmtProcessor();
        isTimeout = false;
        iterations = 0;
        csCallEdges = 0;
        progressLines = 0;
        progressCounters.reset();
        addOrigin = ORIGIN_OTHER;
        Arrays.fill(addsByOrigin, 0);
        solveStartNanos = System.nanoTime();
        lastProgressNanos = solveStartNanos;
        liveCensusClock = LiveCensusClock.of(options.getInt("census-interval"), solveStartNanos);
        blockProbe = CallBlockProbe.of(options.getString("call-block-probe"),
                csManager.getObjectIndexer());
        liveCensuses = 0;
        liveCensusNanos = 0;
        lastLiveCensus = null;
        lastLiveOwners = null;
        if (timeLimit != UNLIMITED) {
            timeLimiter = new TimeLimiter(timeLimit);
            timeLimiter.countDown();
        }
        plugin.onStart();
    }

    private WorkList newWorkList() {
        return new WorkList(ptsFactory, options.getBoolean("pack-pending-deltas"),
                counting, options.getInt("pack-cold-sets"));
    }

    private class TimeLimiter {

        private static final long MILLIS_FACTOR = 1000;

        private final Thread thread;

        /**
         * @param seconds the time limit.
         */
        private TimeLimiter(long seconds) {
            thread = new Thread(() -> {
                try {
                    Thread.sleep(seconds * MILLIS_FACTOR);
                } catch (InterruptedException ignored) {
                }
                isTimeout = true;
            });
        }

        /**
         * Starts count down.
         */
        private void countDown() {
            thread.start();
        }

        /**
         * Stops count down.
         */
        private void stop() {
            thread.interrupt();
        }
    }

    /**
     * Packs the sets that left the cold windows (option
     * {@code pack-cold-sets}). Runs only between two polls: there no
     * caller iterates a points-to set or a pending delta, and no fan-out
     * is open.
     */
    private void packColdSets() {
        if (coldSoleSets != null && packColdSole != null) {
            coldSoleSets.drain(packColdSole);
        }
        workList.packColdDeltas();
    }

    /**
     * Processes work list entries until the work list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty() && !isTimeout) {
            // phase starts
            while (!workList.isEmpty() && !isTimeout) {
                if ((++iterations & progressCheckMask) == 0) {
                    if (progressIntervalNanos != 0) {
                        checkProgress();
                    }
                    if (liveCensusClock.isOn()) {
                        checkLiveCensus();
                    }
                }
                packColdSets();
                if (workList.hasCallEdge()) {
                    processCallEdge(workList.pollCallEdge());
                } else {
                    Pointer p = workList.pollPointer();
                    PointsToSet pts = workList.takePolledDelta();
                    int polledSize = counting ? pts.size() : 0;
                    PointsToSet diff = propagate(p, pts);
                    if (counting) {
                        workList.recordPropagation(polledSize, diff.size());
                    }
                    if (!diff.isEmpty() && p instanceof CSVar v) {
                        processInstanceStore(v, diff);
                        processInstanceLoad(v, diff);
                        processArrayStore(v, diff);
                        processArrayLoad(v, diff);
                        if (counting) {
                            addOrigin = ORIGIN_PROCESS_CALL;
                            try {
                                processCall(v, diff);
                            } finally {
                                addOrigin = ORIGIN_OTHER;
                            }
                        } else {
                            processCall(v, diff);
                        }
                        plugin.onNewPointsToSet(v, diff);
                    }
                }
            }
            plugin.onPhaseFinish();
        }
        stoppedByTimeLimit = !workList.isEmpty() && isTimeout;
        logger.info("Work list: {}", workListCountersLine());
        if (liveCensuses > 0) {
            logger.info("Censuses during the solve: {}, took {} ms in total"
                            + " (included in the solve time and a time limit)",
                    liveCensuses, liveCensusNanos / NANOS_PER_MS);
        }
        if (stoppedByTimeLimit) {
            logger.warn("Pointer analysis stops early as it reaches time limit ({} seconds)," +
                    " and the result may be unsound!", timeLimit);
        } else if (timeLimiter != null) { // finish normally but time limiter is still running
            timeLimiter.stop();
        }
        if (interner != null) {
            logger.info("Points-to set interner: {} shared sets, {}",
                    interner.size(), interner.counters());
            if (coldSoleSets != null) {
                logger.info("Cold sole sets: packed={} packed_sole_writes={}",
                        interner.solePacks(), interner.packedSoleWrites());
            }
        }
        if (counting) {
            logger.info("Solver counters: {}", countersLine());
            logger.info("Type filter guards: {}",
                    TypeFilter.guardsBlock(typeFilters.values(), true, GUARD_LINES));
        }
        if (blockProbe != null) {
            logger.info("Call block probe: {}", blockProbe.line());
        }
        if (options.getBoolean("census")) {
            census = SolverCensus.take(csManager, callGraph);
            owners = takeOwners();
        }
        if (options.getBoolean("release-solver-state")) {
            releaseSolverState();
            plugin.onRelease();
        }
        plugin.onFinish();
    }

    /**
     * Takes a census when {@link #liveCensusClock} says one is due: at the
     * point between two polls of the work list, where no transfer is half
     * done. The census only reads the solver state, so the solve goes on
     * with the same results and the same order (a time limit, if set,
     * also counts the time of the census).
     */
    private void checkLiveCensus() {
        long start = System.nanoTime();
        String reason = liveCensusClock.due(start);
        if (reason == null) {
            return;
        }
        logger.info("Census during the solve at {} s ({}), iteration {}",
                (start - solveStartNanos) / NANOS_PER_SECOND, reason, iterations);
        lastLiveCensus = SolverCensus.take(csManager, callGraph);
        lastLiveOwners = takeOwners();
        if (counting) {
            logger.info("Work list: {}", workList.countersLine());
            if (interner != null) {
                logger.info("Points-to set interner: {} shared sets, {}",
                        interner.size(), interner.counters());
            }
            logger.info("Solver counters: {}", countersLine());
        }
        if (blockProbe != null) {
            logger.info("Call block probe: {}", blockProbe.line());
        }
        plugin.onCensus();
        ++liveCensuses;
        long end = System.nanoTime();
        liveCensusNanos += end - start;
        liveCensusClock.taken(end);
        logger.info("Census during the solve took {} ms", (end - start) / NANOS_PER_MS);
    }

    /**
     * Takes and logs the heap owner census of the pointers' points-to sets
     * (mock pointers included), the pending work list deltas and the
     * exception sets of the reachable methods' throw results.
     */
    private HeapOwnerCensus takeOwners() {
        HeapOwnerCensus heap = new HeapOwnerCensus();
        csManager.pointers().forEach(p -> heap.addPointer(p.getPointsToSet()));
        csManager.mockPointers().forEach(p -> heap.addPointer(p.getPointsToSet()));
        workList.addPendingTo(heap);
        callGraph.reachableMethods().forEach(m -> {
            CSMethodThrowResult result = m.getThrowResult();
            if (result != null) {
                result.addTo(heap);
            }
        });
        heap.finish();
        logger.info("{}", heap);
        return heap;
    }

    /**
     * @return the counters of the work list's pointer entries, as logged at
     * the end of the solve
     */
    String workListCountersLine() {
        return workList.countersLine();
    }

    /**
     * Logs one progress line when at least the progress interval has passed
     * since the last line (or the start of the solve). Reads only O(1) sizes
     * and counters.
     */
    private void checkProgress() {
        long now = System.nanoTime();
        if (now - lastProgressNanos < progressIntervalNanos) {
            return;
        }
        lastProgressNanos = now;
        ++progressLines;
        Runtime runtime = Runtime.getRuntime();
        long heapUsedMb = (runtime.totalMemory() - runtime.freeMemory()) / BYTES_PER_MB;
        long elapsedS = (now - solveStartNanos) / NANOS_PER_SECOND;
        long extPending = progressCounters.getPendingEntries();
        long extWaves = progressCounters.getWaves();
        long extDrained = progressCounters.getEntriesDrained();
        if (extPending == 0 && extWaves == 0 && extDrained == 0) {
            logger.info(PROGRESS_FORMAT,
                    elapsedS, iterations, workList.pointerEntryCount(),
                    workList.callEdgeCount(), callGraph.getNumberOfMethods(),
                    reachableMethods.size(), csCallEdges,
                    csManager.getNumberOfPointers(), heapUsedMb);
        } else {
            logger.info(PROGRESS_EXT_FORMAT,
                    elapsedS, iterations, workList.pointerEntryCount(),
                    workList.callEdgeCount(), callGraph.getNumberOfMethods(),
                    reachableMethods.size(), csCallEdges,
                    csManager.getNumberOfPointers(), heapUsedMb,
                    extPending, extWaves, extDrained,
                    progressCounters.getEdgesVisited(),
                    progressCounters.getEmptyDiffs());
        }
        if (counting) {
            // O(1) counters only; the pending walk and the filter sums are
            // logged at the finish
            logger.info("PTA progress counters: {} polled_bits={} diff_bits={}"
                            + " empty_diff_polls={} merges_unchanged={}",
                    addsLine(), workList.polledBits(), workList.diffBits(),
                    workList.emptyDiffPolls(), workList.mergesUnchanged());
        }
        if (blockProbe != null) {
            // reads only the probe's counters, so a run needs no census
            logger.info("Call block probe: {}", blockProbe.line());
        }
    }

    private String addsLine() {
        StringBuilder line = new StringBuilder("adds");
        for (int i = 0; i < ORIGIN_NAMES.length; ++i) {
            line.append(' ').append(ORIGIN_NAMES[i]).append('=').append(addsByOrigin[i]);
        }
        return line.toString();
    }

    /**
     * @return the measurement counters of the solver, the type filters and
     * the interner in one line.
     */
    String countersLine() {
        StringBuilder line = new StringBuilder(addsLine());
        line.append("; type filters ")
                .append(TypeFilter.statsLine(typeFilters.values(), counting));
        if (interner != null) {
            line.append("; interner ").append(interner.formCopiesLine());
        }
        return line.toString();
    }

    /**
     * @return the points-to work added so far from {@code origin}, one of
     * the {@code ORIGIN_} indexes; zero unless the counters are kept.
     */
    long addsFrom(int origin) {
        return addsByOrigin[origin];
    }

    /**
     * @return the work list, for reading its measurement counters.
     */
    WorkList getWorkListForCounters() {
        return workList;
    }

    /**
     * The progress check that plugins run during their own drains
     * ({@link ProgressCounters#drainEntry(long)}): a no-op when the progress
     * line is off.
     */
    private void checkProgressIfOn() {
        if (progressIntervalNanos != 0) {
            checkProgress();
        }
    }

    /**
     * Releases the state that only the solve reads, before the plugins'
     * onRelease and onFinish: the work list (empty at the fixed point;
     * after a time-limit stop its entries would never be processed either),
     * the out-edge dedup sets of all pointers, mock pointers included (new
     * edges are refused) and the type filter memos (pure caches, rebuilt by
     * a later application). New work is refused afterwards, also for
     * pointers created later, whose dedup state is live.
     * <p>
     * With the option {@code release-pointer-flow-graph} it also drops the
     * out edges of those pointers, the pointer flow graph. The points-to
     * sets and the call graph do not read it; its readers after the solve
     * are the object flow graph of the result (Zipper, the taint flow
     * graph), the taint plugin's and the reflective-args verifier's
     * onFinish, and plugins that walk out edges. Each of them then fails
     * with an {@link IllegalStateException} instead of reading an empty
     * graph. Without the option the out edges stay.
     */
    private void releaseSolverState() {
        solverStateReleased = true;
        // the solver refuses new work from here on: no cold window is needed
        workList = new WorkList(ptsFactory, options.getBoolean("pack-pending-deltas"),
                counting, 0);
        coldSoleSets = null;
        packColdSole = null;
        csManager.pointers().forEach(Pointer::releaseEdgeDedup);
        csManager.mockPointers().forEach(Pointer::releaseEdgeDedup);
        if (options.getBoolean("release-pointer-flow-graph")) {
            csManager.pointers().forEach(Pointer::releaseOutEdges);
            csManager.mockPointers().forEach(Pointer::releaseOutEdges);
        }
        typeFilters.values().forEach(TypeFilter::releaseMemo);
        TypeFilter.clearMemos();
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        Set<Predicate<CSObj>> filters = pointer.getFilters();
        if (!filters.isEmpty()) {
            // apply filters (of the pointer) on pointsToSet
            pointsToSet = pointsToSet.objects()
                    .filter(o -> filters.stream().allMatch(f -> f.test(o)))
                    .collect(ptsFactory::make, PointsToSet::addObject, PointsToSet::addAll);
        }
        PointsToSetInterner sharing = interner;
        PointsToSet computed = sharing != null
                ? sharing.addAllDiff(pointer, pointsToSet)
                : getPointsToSetOf(pointer).addAllDiff(pointsToSet);
        PointsToSet diff = filters.isEmpty()
                ? sameLargeSetOr(computed, pointsToSet)
                : computed;
        if (coldSoleSets != null && sharing != null && !diff.isEmpty()
                && sharing.holdsUnpackedSole(pointer)) {
            coldSoleSets.touch(pointer);
        }
        if (!diff.isEmpty()) {
            try {
                pointer.forEachOutTransfer((edge, target, transfer) ->
                        addFanOutPointsTo(target, transfer,
                                deltaTransfers.apply(edge, transfer, diff)));
            } finally {
                workList.endFanOut();
                deltaTransfers.finish(pointer, diff);
            }
        }
        return diff;
    }

    /**
     * The difference is a subset of the propagated delta, so a difference
     * of the delta's size equals the delta. When both are large sets, which
     * iterate in index order, the delta serves as the difference: the work
     * list can then pass the same set on to the successors by reference
     * (see {@link WorkList#addFanOutEntry}).
     *
     * @return {@code delta} if it equals {@code diff} and both are large,
     * else {@code diff}
     */
    private PointsToSet sameLargeSetOr(PointsToSet diff, PointsToSet delta) {
        if (diff != delta && ptsFactory.isLarge(delta) && ptsFactory.isLarge(diff)
                && diff.size() == delta.size()) {
            return delta;
        }
        return diff;
    }

    /**
     * Processes instance stores when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceStore(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            Var fromVar = store.getRValue();
            if (propTypes.isAllowed(fromVar)) {
                CSVar from = csManager.getCSVar(context, fromVar);
                JField field = store.getFieldRef().resolveNullable();
                if (field != null) {
                    pts.forEach(baseObj -> {
                        if (baseObj.getObject().isFunctional()) {
                            InstanceField instField = csManager.getInstanceField(baseObj, field);
                            addPFGEdge(from, instField, FlowKind.INSTANCE_STORE);
                        }
                    });
                }
            }
        }
    }

    /**
     * Processes instance loads when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceLoad(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            if (propTypes.isAllowed(toVar)) {
                CSVar to = csManager.getCSVar(context, toVar);
                JField field = load.getFieldRef().resolveNullable();
                if (field != null) {
                    pts.forEach(baseObj -> {
                        if (baseObj.getObject().isFunctional()) {
                            InstanceField instField = csManager.getInstanceField(baseObj, field);
                            addPFGEdge(instField, to, FlowKind.INSTANCE_LOAD);
                        }
                    });
                }
            }
        }
    }

    /**
     * Processes array stores when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayStore(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        // consecutive stores of one variable share its lookup
        @Nullable CSVar lastFrom = null;
        try {
            for (StoreArray store : var.getStoreArrays()) {
                Var rvalue = store.getRValue();
                if (propTypes.isAllowed(rvalue)) {
                    if (lastFrom == null || lastFrom.getVar() != rvalue) {
                        lastFrom = csManager.getCSVar(context, rvalue);
                    }
                    CSVar from = lastFrom;
                    pts.forEach(array -> {
                        if (array.getObject().isFunctional()) {
                            addArrayStoreEdge(from, csManager.getArrayIndex(array));
                        }
                    });
                }
            }
        } finally {
            deltaTransfers.clear();
        }
    }

    /**
     * {@link #addPFGEdge(PointerFlowEdge, Type)} for an array store edge,
     * guarded by the element type of the array as Java arrays are
     * covariant. The type filter's result on the points-to set of the
     * source is shared through {@link #deltaTransfers} by the new edges of
     * one {@link #processArrayStore} call that carry the same filter: that
     * set does not change during the call (new objects only enter the work
     * list), and the work list only reads the result (it copies it into a
     * new entry or adds it to a pending one).
     */
    private void addArrayStoreEdge(CSVar from, ArrayIndex arrayIndex) {
        checkAcceptsWork();
        TypeFilter filter = typeFilterOf(arrayIndex.getType());
        PointerFlowEdge edge = pointerFlowGraph.addEdge(
                new PointerFlowEdge(FlowKind.ARRAY_STORE, from, arrayIndex), filter);
        if (edge != null) {
            PointsToSet targetSet = deltaTransfers.apply(
                    edge, filter, getPointsToSetOf(from));
            if (!targetSet.isEmpty()) {
                addPointsTo(edge.target(), targetSet);
            }
        }
    }

    /**
     * Processes array loads when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayLoad(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (LoadArray load : var.getLoadArrays()) {
            Var lvalue = load.getLValue();
            if (propTypes.isAllowed(lvalue)) {
                CSVar to = csManager.getCSVar(context, lvalue);
                pts.forEach(array -> {
                    if (array.getObject().isFunctional()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        addPFGEdge(arrayIndex, to, FlowKind.ARRAY_LOAD);
                    }
                });
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv the receiver variable
     * @param pts  set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, PointsToSet pts) {
        Context context = recv.getContext();
        Var var = recv.getVar();
        for (Invoke callSite : var.getInvokes()) {
            // the CS call site, looked up once per call site and only at
            // its first resolved callee (where the lookup always happened)
            CSCallSite[] csCallSiteOnce = new CSCallSite[1];
            CallBlockProbe probe = blockProbe;
            CallBlockProbe.Batch batch = probe == null ? null
                    : probe.begin(callSite, CallBlockProbe.EdgeClass.PLAIN);
            pts.forEach(recvObj -> {
                // resolve callee
                JMethod callee = CallGraphs.resolveCallee(
                        recvObj.getObject().getType(), callSite);
                if (callee != null) {
                    // select context
                    CSCallSite csCallSite = csCallSiteOnce[0];
                    if (csCallSite == null) {
                        csCallSite = csManager.getCSCallSite(context, callSite);
                        csCallSiteOnce[0] = csCallSite;
                    }
                    if (trivialGetters && inlinesGetter(csCallSite, callee, recvObj, batch)) {
                        return;
                    }
                    Context calleeContext = contextSelector.selectContext(
                            csCallSite, recvObj, callee);
                    // build call edge
                    CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                    CallKind kind = CallGraphs.getCallKind(callSite);
                    // an edge already in the call graph would be a no-op
                    // when polled (processCallEdge), so it is not allocated
                    Edge<CSCallSite, CSMethod> edge = csCallSite.hasPlainEdge(kind, csCallee)
                            ? null : new Edge<>(kind, csCallSite, csCallee);
                    if (batch != null) {
                        batch.offer(recvObj, csCallee, edge);
                    }
                    if (edge != null) {
                        addCallEdge(edge);
                    }
                    // pass receiver object to *this* variable
                    if (!isIgnored(callee)) {
                        addVarPointsTo(calleeContext, callee.getIR().getThis(),
                                recvObj);
                    }
                } else {
                    plugin.onUnresolvedCall(recvObj, context, callSite);
                }
            });
            if (probe != null && batch != null) {
                probe.end(batch);
            }
        }
    }

    /**
     * Takes a call to a trivial getter ({@link TrivialGetter}) as a load at
     * the call site (option {@code trivial-getters}): the call site gets one
     * plain call edge to the callee in the empty context, and the callee's
     * {@code this} variable gets no receiver object, so the callee has no
     * context of a receiver. For a getter of an instance field {@code f},
     * the receiver object {@code o} adds the load {@code o.f -> lhs} with
     * the checks of the getter's own load and return. The return passing of
     * the edge is kept: a static field or {@code null} reaches the result
     * through the callee's statements in the empty context. With object
     * sensitivity whose callee context fixes the receiver object (k-obj with
     * heap contexts of length k - 1) the result is the same as the call's;
     * otherwise it is a subset of it, as the call merges the receivers of
     * one callee context.
     *
     * @param recvObj the receiver object, null for a static call
     * @param batch   the block probe's batch of the call site, null when the
     *                probe is off; it gets the getter's edge
     * @return whether the call was taken as a load; false when the callee is
     * not a trivial getter or is ignored
     */
    private boolean inlinesGetter(CSCallSite csCallSite, JMethod callee,
                                  @Nullable CSObj recvObj,
                                  CallBlockProbe.@Nullable Batch batch) {
        if (isIgnored(callee)) {
            return false;
        }
        TrivialGetter getter = getterShapes.computeIfAbsent(callee, TrivialGetter::of);
        if (getter.form() == TrivialGetter.Form.NONE) {
            return false;
        }
        Invoke callSite = csCallSite.getCallSite();
        CSMethod csCallee = csManager.getCSMethod(contextSelector.getEmptyContext(), callee);
        CallKind kind = CallGraphs.getCallKind(callSite);
        Edge<CSCallSite, CSMethod> edge = csCallSite.hasPlainEdge(kind, csCallee)
                ? null : new Edge<>(kind, csCallSite, csCallee);
        if (batch != null) {
            batch.offer(recvObj, csCallee, edge);
        }
        if (edge != null) {
            addCallEdge(edge);
        }
        if (getter.form() == TrivialGetter.Form.INSTANCE_FIELD) {
            LoadField load = Objects.requireNonNull(getter.load());
            CSObj receiver = Objects.requireNonNull(recvObj,
                    "an instance field getter is called without a receiver");
            Var lhs = callSite.getResult();
            if (lhs != null && receiver.getObject().isFunctional()
                    && propTypes.isAllowed(lhs) && propTypes.isAllowed(load.getLValue())) {
                JField field = load.getFieldRef().resolveNullable();
                if (field != null) {
                    addPFGEdge(csManager.getInstanceField(receiver, field),
                            csManager.getCSVar(csCallSite.getContext(), lhs),
                            FlowKind.INSTANCE_LOAD);
                }
            }
        }
        return true;
    }

    private void processCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (callGraph.addEdge(edge)) {
            ++csCallEdges;
            if (blockProbe != null) {
                blockProbe.edgeAdded(edge);
            }
            // the PFG edges this call edge adds, for the block probe
            int argEdges = 0;
            int returnEdges = 0;
            // process new call edge
            CSMethod csCallee = edge.getCallee();
            addCSMethod(csCallee);
            if (edge.getKind() != CallKind.OTHER
                    && !isIgnored(csCallee.getMethod())) {
                Context callerCtx = edge.getCallSite().getContext();
                Invoke callSite = edge.getCallSite().getCallSite();
                Context calleeCtx = csCallee.getContext();
                JMethod callee = csCallee.getMethod();
                InvokeExp invokeExp = callSite.getInvokeExp();
                // pass arguments to parameters
                int argCount = invokeExp.getArgCount();
                int paramCount = callee.getParamCount();
                if (argCount == paramCount) {
                    for (int i = 0; i < argCount; ++i) {
                        Var arg = invokeExp.getArg(i);
                        if (propTypes.isAllowed(arg)) {
                            Var param = callee.getIR().getParam(i);
                            CSVar argVar = csManager.getCSVar(callerCtx, arg);
                            CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                            addPFGEdge(argVar, paramVar, FlowKind.PARAMETER_PASSING);
                            ++argEdges;
                        }
                    }
                } else {
                    // A call site to a signature-polymorphic method (JLS 15.12.3),
                    // e.g., MethodHandle.linkToStatic, may have more arguments
                    // than the declared parameters of the resolved method, which
                    // declares a single varargs parameter (Object...). The declared
                    // parameters are fictitious for such methods, thus we skip
                    // parameter passing for these calls.
                    logger.debug("Skip parameter passing from {} to {}:"
                            + " {} arguments vs. {} parameters",
                            callSite, callee, argCount, paramCount);
                }
                // pass results to LHS variable
                Var lhs = callSite.getResult();
                if (lhs != null && propTypes.isAllowed(lhs)) {
                    CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
                    for (Var ret : callee.getIR().getReturnVars()) {
                        if (propTypes.isAllowed(ret)) {
                            CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                            addPFGEdge(csRet, csLHS, FlowKind.RETURN);
                            ++returnEdges;
                        }
                    }
                }
            }
            if (blockProbe != null) {
                blockProbe.edgePolled(edge, argEdges, returnEdges);
            }
            plugin.onNewCallEdge(edge);
        } else if (blockProbe != null) {
            blockProbe.edgePolled(edge, 0, 0);
        }
    }

    private boolean isIgnored(JMethod method) {
        return ignoredMethods.contains(method) ||
                onlyApp && !method.isApplication();
    }

    /**
     * Processes new reachable methods.
     */
    private void processNewMethod(JMethod method) {
        if (reachableMethods.add(method)) {
            plugin.onNewMethod(method);
            method.getIR().forEach(stmt -> plugin.onNewStmt(stmt, method));
        }
    }

    private class StmtProcessor {

        /**
         * Information shared by all visitors.
         */
        private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();

        private final Map<New, Invoke> registerInvokes = Maps.newMap();

        private final JMethod finalize = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZE));

        private final MethodRef finalizeRef = finalize.getRef();

        private final MethodRef registerRef = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();

        /**
         * Processes given Stmts in given CSMethod.
         */
        private void process(CSMethod csMethod, Collection<Stmt> stmts) {
            StmtVisitor<Void> visitor = new Visitor(csMethod);
            stmts.forEach(stmt -> stmt.accept(visitor));
        }

        /**
         * Visitor that contains actual processing logics.
         */
        private class Visitor implements StmtVisitor<Void> {

            private final CSMethod csMethod;

            private final Context context;

            private Visitor(CSMethod csMethod) {
                this.csMethod = csMethod;
                this.context = csMethod.getContext();
            }

            @Override
            public Void visit(New stmt) {
                // obtain context-sensitive heap object
                NewExp rvalue = stmt.getRValue();
                Obj obj = heapModel.getObj(stmt);
                Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
                addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                if (rvalue instanceof NewMultiArray) {
                    processNewMultiArray(stmt, heapContext, obj);
                }
                if (hasOverriddenFinalize(rvalue)) {
                    processFinalizer(stmt);
                }
                return null;
            }

            private void processNewMultiArray(
                    New allocSite, Context arrayContext, Obj array) {
                NewMultiArray newMultiArray = (NewMultiArray) allocSite.getRValue();
                Obj[] arrays = newArrays.computeIfAbsent(newMultiArray, nma -> {
                    ArrayType type = nma.getType();
                    Obj[] newArrays = new MockObj[nma.getLengthCount() - 1];
                    for (int i = 1; i < nma.getLengthCount(); ++i) {
                        type = (ArrayType) type.elementType();
                        newArrays[i - 1] = heapModel.getMockObj(MULTI_ARRAY_DESC,
                                allocSite, type, allocSite.getContainer());
                    }
                    return newArrays;
                });
                for (Obj newArray : arrays) {
                    Context elemContext = contextSelector
                            .selectHeapContext(csMethod, newArray);
                    CSObj arrayObj = csManager.getCSObj(arrayContext, array);
                    ArrayIndex arrayIndex = csManager.getArrayIndex(arrayObj);
                    addPointsTo(arrayIndex, elemContext, newArray);
                    array = newArray;
                    arrayContext = elemContext;
                }
            }

            private boolean hasOverriddenFinalize(NewExp newExp) {
                return !finalize.equals(
                        hierarchy.dispatch(newExp.getType(), finalizeRef));
            }

            /**
             * Call Finalizer.register() at allocation sites of objects
             * which override Object.finalize() method.
             * NOTE: finalize() has been deprecated since Java 9, and
             * will eventually be removed.
             */
            private void processFinalizer(New stmt) {
                Invoke registerInvoke = registerInvokes.computeIfAbsent(stmt, s -> {
                    InvokeStatic callSite = new InvokeStatic(registerRef,
                            Collections.singletonList(s.getLValue()));
                    Invoke invoke = new Invoke(csMethod.getMethod(), callSite);
                    invoke.setLineNumber(stmt.getLineNumber());
                    return invoke;
                });
                processInvokeStatic(registerInvoke);
            }

            private void processInvokeStatic(Invoke callSite) {
                JMethod callee = CallGraphs.resolveCallee(null, callSite);
                if (callee != null) {
                    CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                    // a static call is no class of the block probe
                    if (trivialGetters && inlinesGetter(csCallSite, callee, null, null)) {
                        return;
                    }
                    Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                    CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                    addCallEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee));
                }
            }

            @Override
            public Void visit(AssignLiteral stmt) {
                Literal literal = stmt.getRValue();
                Type type = literal.getType();
                if (type instanceof ClassType) {
                    // here we only generate objects of ClassType
                    Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                    Context heapContext = contextSelector
                            .selectHeapContext(csMethod, obj);
                    addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                }
                return null;
            }

            @Override
            public Void visit(Copy stmt) {
                Var rvalue = stmt.getRValue();
                if (propTypes.isAllowed(rvalue)) {
                    CSVar from = csManager.getCSVar(context, rvalue);
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(from, to, FlowKind.LOCAL_ASSIGN);
                }
                return null;
            }

            @Override
            public Void visit(Phi stmt) {
                PhiExp rvalue = stmt.getRValue();
                if (propTypes.isAllowed(rvalue)) {
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    rvalue.getSourceAndVar().forEach(pair -> {
                        CSVar from = csManager.getCSVar(context, pair.second());
                        addPFGEdge(from, to, FlowKind.LOCAL_ASSIGN);
                    });
                }
                return null;
            }

            @Override
            public Void visit(Cast stmt) {
                CastExp cast = stmt.getRValue();
                if (propTypes.isAllowed(cast.getValue())) {
                    CSVar from = csManager.getCSVar(context, cast.getValue());
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(new PointerFlowEdge(
                            FlowKind.CAST, from, to),
                            cast.getType());
                }
                return null;
            }

            /**
             * Processes static load.
             */
            @Override
            public Void visit(LoadField stmt) {
                if (stmt.isStatic() && propTypes.isAllowed(stmt.getRValue())) {
                    JField field = stmt.getFieldRef().resolveNullable();
                    if (field != null) {
                        StaticField sfield = csManager.getStaticField(field);
                        CSVar to = csManager.getCSVar(context, stmt.getLValue());
                        addPFGEdge(sfield, to, FlowKind.STATIC_LOAD);
                    }
                }
                return null;
            }

            /**
             * Processes static store.
             */
            @Override
            public Void visit(StoreField stmt) {
                if (stmt.isStatic() && propTypes.isAllowed(stmt.getRValue())) {
                    JField field = stmt.getFieldRef().resolveNullable();
                    if (field != null) {
                        StaticField sfield = csManager.getStaticField(field);
                        CSVar from = csManager.getCSVar(context, stmt.getRValue());
                        addPFGEdge(from, sfield, FlowKind.STATIC_STORE);
                    }
                }
                return null;
            }

            /**
             * Processes static invocation.
             */
            @Override
            public Void visit(Invoke stmt) {
                if (stmt.isStatic()) {
                    processInvokeStatic(stmt);
                }
                return null;
            }
        }
    }

    // ---------- solver logic ends ----------

    @Override
    public void addPointsTo(Pointer pointer, PointsToSet pts) {
        checkAcceptsWork();
        if (counting) {
            ++addsByOrigin[addOrigin];
        }
        workList.addEntry(pointer, pts);
    }

    /**
     * {@link #addPointsTo(Pointer, PointsToSet)} counted under
     * {@code origin} when the counters are kept.
     */
    private void addPointsToFrom(int origin, Pointer pointer, PointsToSet pts) {
        if (!counting) {
            addPointsTo(pointer, pts);
            return;
        }
        int saved = addOrigin;
        addOrigin = origin;
        try {
            addPointsTo(pointer, pts);
        } finally {
            addOrigin = saved;
        }
    }

    /**
     * {@link #addPointsTo(Pointer, PointsToSet)} for one out-edge of a
     * propagation. The result of {@link Identity} (the delta) and of a
     * {@link TypeFilter} (a new set, or the delta) is not changed before
     * the propagation ends, so its new entries may share one stored
     * delta; another transfer's result might be a set it reuses.
     */
    private void addFanOutPointsTo(Pointer target, Transfer transfer, PointsToSet pts) {
        if (transfer == Identity.INSTANCE || transfer.getClass() == TypeFilter.class) {
            checkAcceptsWork();
            if (counting) {
                ++addsByOrigin[ORIGIN_FAN_OUT];
            }
            workList.addFanOutEntry(target, pts);
        } else {
            addPointsToFrom(ORIGIN_FAN_OUT, target, pts);
        }
    }

    /**
     * @throws IllegalStateException if {@link #releaseSolverState()} ran:
     *                               the solver would never process new work
     */
    private void checkAcceptsWork() {
        if (solverStateReleased) {
            throw new IllegalStateException("the solver state was released"
                    + " after the fixed point; new work would never be processed");
        }
    }

    @Override
    public void addPointsTo(Pointer pointer, CSObj csObj) {
        checkAcceptsWork();
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        addPointsTo(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
        checkAcceptsWork();
        addPointsTo(pointer, csManager.getCSObj(heapContext, obj));
    }

    @Override
    public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
        checkAcceptsWork();
        addPointsTo(csManager.getCSVar(context, var), pts);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, CSObj csObj) {
        checkAcceptsWork();
        addPointsTo(csManager.getCSVar(context, var), csObj);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
        checkAcceptsWork();
        addPointsTo(csManager.getCSVar(context, var), heapContext, obj);
    }

    @Override
    public void addPointerFilter(Pointer pointer, Predicate<CSObj> filter) {
        pointer.addFilter(filter);
    }

    @Override
    public void addPFGEdge(PointerFlowEdge edge, Type type) {
        checkAcceptsWork();
        addPFGEdge(edge, typeFilterOf(type));
    }

    /**
     * @return the type filter of the guard type, created on first use
     */
    private TypeFilter typeFilterOf(Type type) {
        TypeFilter filter = typeFilters.get(type);
        if (filter == null) {
            filter = new TypeFilter(type, this);
            if (counting) {
                filter.enableStats();
            }
            typeFilters.put(type, filter);
        }
        return filter;
    }

    @Override
    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer) {
        checkAcceptsWork();
        edge = pointerFlowGraph.addEdge(edge, transfer);
        if (edge != null) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                addPointsToFrom(ORIGIN_INITIAL_FLOW, edge.target(), targetSet);
            }
        }
    }

    @Override
    public void addEntryPoint(EntryPoint entryPoint) {
        checkAcceptsWork();
        Context entryCtx = contextSelector.getEmptyContext();
        JMethod entryMethod = entryPoint.method();
        CSMethod csEntryMethod = csManager.getCSMethod(entryCtx, entryMethod);
        callGraph.addEntryMethod(csEntryMethod);
        addCSMethod(csEntryMethod);
        IR ir = entryMethod.getIR();
        ParamProvider paramProvider = entryPoint.paramProvider();
        // pass this objects
        if (!entryMethod.isStatic()) {
            for (Obj thisObj : paramProvider.getThisObjs()) {
                addVarPointsTo(entryCtx, ir.getThis(), entryCtx, thisObj);
            }
        }
        // pass parameter objects
        for (int i = 0; i < entryMethod.getParamCount(); ++i) {
            Var param = ir.getParam(i);
            if (propTypes.isAllowed(param)) {
                for (Obj paramObj : paramProvider.getParamObjs(i)) {
                    addVarPointsTo(entryCtx, param, entryCtx, paramObj);
                }
            }
        }
        // pass field objects
        paramProvider.getFieldObjs().forEach((base, field, obj) -> {
            CSObj csBase = csManager.getCSObj(entryCtx, base);
            InstanceField iField = csManager.getInstanceField(csBase, field);
            addPointsTo(iField, entryCtx, obj);
        });
        // pass array objects
        paramProvider.getArrayObjs().forEach((array, elem) -> {
            CSObj csArray = csManager.getCSObj(entryCtx, array);
            ArrayIndex arrayIndex = csManager.getArrayIndex(csArray);
            addPointsTo(arrayIndex, entryCtx, elem);
        });
    }

    @Override
    public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
        checkAcceptsWork();
        workList.addEntry(edge);
    }

    @Override
    public void addCSMethod(CSMethod csMethod) {
        checkAcceptsWork();
        if (callGraph.addReachableMethod(csMethod)) {
            // process new reachable context-sensitive method
            JMethod method = csMethod.getMethod();
            if (isIgnored(method)) {
                return;
            }
            processNewMethod(method);
            addStmts(csMethod, method.getIR().getStmts());
            plugin.onNewCSMethod(csMethod);
        }
    }

    @Override
    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {
        checkAcceptsWork();
        stmtProcessor.process(csMethod, stmts);
    }

    @Override
    public void addIgnoredMethod(JMethod method) {
        ignoredMethods.add(method);
    }

    @Override
    public void initializeClass(JClass cls) {
        if (cls == null || initializedClasses.contains(cls)) {
            return;
        }
        checkAcceptsWork();
        // initialize super class
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        // TODO: initialize the superinterfaces which
        //  declare default methods
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            // addCSMethod() may trigger initialization of more
            // classes. So cls must be added before addCSMethod(),
            // otherwise, infinite recursion may occur.
            initializedClasses.add(cls);
            CSMethod csMethod = csManager.getCSMethod(
                    contextSelector.getEmptyContext(), clinit);
            addCSMethod(csMethod);
        }
    }

    @Override
    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(
                    propTypes, csManager, heapModel,
                    callGraph, pointerFlowGraph);
        }
        return result;
    }
}
