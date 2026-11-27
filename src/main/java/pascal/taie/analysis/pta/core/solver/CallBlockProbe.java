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
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.config.ConfigException;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.util.Indexer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.ToIntFunction;

/**
 * The block-sharing probe of the call hub design (option
 * {@code call-block-probe}, px/s116 steps L0 and L1). It only counts: it adds
 * no pointer, edge or context and changes no order.
 * <p>
 * A <em>batch</em> is what one event of an edge source offers at one invoke:
 * the receiver diff of {@link DefaultSolver}'s processCall at one call site,
 * one receiver grouping of the lambda analysis, one reflective dispatch. Its
 * content is the set of pairs (receiver object, callee node) it offers. A
 * callee node of a batch is <em>fresh</em> when the batch's edge to it is
 * neither in the call graph nor offered by an earlier batch whose edge is
 * still in the work list: these are the edges the batch makes today. The
 * probe simulates hubs on these batches, per invoke and edge class:
 * <ul>
 * <li>phase 1 (modes {@code p1}, {@code p1b}): a batch whose content equals
 * an earlier block of the invoke joins it (one hub reference), otherwise it
 * makes a new block (one hub reference plus one target edge per distinct
 * callee node); with rule 4 a batch of one pair is not kept and costs its
 * fresh edges (0 or 1);</li>
 * <li>phase 1b (mode {@code p1b}): a miss of two or more pairs is covered by
 * earlier whole blocks of the invoke that are subsets of it (greedy by size,
 * disjoint) plus one remainder block; a cover dearer than the direct edges
 * falls back to them;</li>
 * <li>target hubs (every mode): the key of a batch is its set of fresh callee
 * nodes; a batch with at most one costs its fresh edges, otherwise an equal
 * earlier key of the invoke costs one hub reference and a new key one hub
 * reference plus one target edge per node. Keys are compared exactly (hash,
 * then equality of the invoke, the class and the node sets).</li>
 * </ul>
 * The direct cost of a batch is its number of distinct callee nodes, the
 * edges it makes without hubs when none of them exists yet; {@link
 * Counter#EDGES} counts the call edges the call graph actually took. In
 * phase 1 and 1b callee nodes are told apart by identity hash code (a
 * collision with the same receiver object at the same invoke would merge two
 * pairs) and contents by a 64-bit hash.
 */
public final class CallBlockProbe {

    /** The option value that turns the probe off (the default). */
    static final String NONE = "none";

    /** The modes of the probe, by option value. */
    enum Mode {
        /** Phase 1 and target hubs. */
        P1,
        /** Phase 1, phase 1b and target hubs. */
        P1B,
        /** Target hubs only: no block contents are kept. */
        P1T
    }

    /** The edge classes the probe tells apart. */
    public enum EdgeClass {
        /** Virtual, interface and special calls of processCall. */
        PLAIN,
        /** Lambda instance targets with a captured receiver. */
        LAMBDA_BOUND,
        /** Lambda instance targets dispatched on the first actual argument. */
        LAMBDA_UNBOUND,
        /** Lambda static targets. */
        LAMBDA_STATIC,
        /** Lambda constructor references. */
        LAMBDA_NEW,
        /** Reflective calls. */
        REFLECTIVE
    }

    /** A call edge of a class other than {@link EdgeClass#PLAIN}. */
    public interface Classified {

        EdgeClass blockProbeClass();
    }

    /** The counters kept per edge class. */
    public enum Counter {
        /** Batches with at least one pair. */
        BATCHES,
        /** Distinct pairs offered, summed over the batches. */
        OFFERS,
        /** Distinct callee nodes, summed over the batches. */
        DIRECT,
        /** Call edges the call graph took. */
        EDGES,
        /** Distinct fresh callee nodes, summed over the batches. */
        FRESH,
        /** Batches without a fresh callee node. */
        STALE,
        /**
         * PFG edges the fresh callee nodes get today (processCallEdge's
         * parameter and return edges), summed over the batches.
         */
        W_TODAY,
        P1_HITS,
        P1_BLOCKS,
        P1_BLOCK_PAIRS,
        P1_BLOCK_TARGETS,
        /** Phase-1 misses of one pair (rule 4 makes them direct). */
        P1_SINGLE_MISSES,
        /** Batches of one pair, hit or miss. */
        P1_SINGLES,
        /** Fresh callee nodes of the batches of one pair (0 or 1 each). */
        P1_SINGLE_FRESH,
        P1B_HITS,
        /** Misses covered by at least one earlier block. */
        P1B_COVERED,
        /** Earlier blocks used in covers. */
        P1B_PIECES,
        P1B_BLOCKS,
        /** Pairs of the kept phase-1b blocks. */
        P1B_BLOCK_PAIRS,
        P1B_BLOCK_TARGETS,
        P1B_FALLBACKS,
        /** Phase-1b cost: hub references, target edges and direct edges. */
        P1B_COST,
        /**
         * Target-hub cost: one per batch of one fresh node, one hub
         * reference per batch of more, one target edge per node of a new key.
         */
        P1T_COST,
        /** Batches of exactly one fresh node (direct edges). */
        P1T_SINGLES,
        /** Batches of two or more fresh nodes whose key was known. */
        P1T_HITS,
        /** New keys of two or more fresh nodes: the multi-node hubs. */
        P1T_HUBS,
        /** Batches of two or more fresh nodes: the hub references. */
        P1T_REFS,
        /** Fresh nodes of the new keys: the stored targets. */
        P1T_TARGETS,
        /** Keys with exactly one member (the batch that made them). */
        P1T_HUB1,
        /** Keys with two or more members. */
        P1T_HUB2,
        /** PFG edges ({@link #W_TODAY}) of the batches of one fresh node. */
        W_DIRECT,
        /** PFG edges ({@link #W_TODAY}) of the nodes of new keys. */
        W_TARGETS,
        /** Hub positions (arguments and result) summed over the hub references. */
        W_JOIN,
        /** Hub positions summed over the new keys (their first members; the eager hub pointers). */
        W_JOIN1,
        /** Hub positions summed over the keys with two or more members (the lazy hub pointers). */
        HUB_PTRS2
    }

    /** The blocks per pair that a phase-1b cover looks at. */
    private static final int CHAIN_LIMIT = 64;

    private static final int CLASSES = EdgeClass.values().length;

    private static final int COUNTERS = Counter.values().length;

    private static final Object[] NO_NODES = {};

    private static final Comparator<Object> BY_HASH =
            Comparator.comparingInt(Object::hashCode);

    private final Mode mode;

    private final @Nullable Indexer<CSObj> objects;

    /** The hash of a sorted set of callee nodes (replaced only by tests). */
    private final ToIntFunction<Object[]> nodesHash;

    private final long[] counts = new long[CLASSES * COUNTERS];

    /**
     * The edges fresh batches offered that the solver has not polled yet;
     * an edge the solver polls leaves it ({@link #edgePolled}).
     */
    private final Set<Edge<CSCallSite, CSMethod>> pending = new HashSet<>();

    /** Target hubs: the keys seen. */
    private final Map<TargetKey, TargetKey> targetKeys = new HashMap<>();

    /** Phase 1: the content hashes of the blocks, keyed with their scope. */
    private final LongIntTable phase1Blocks = new LongIntTable();

    /** Phase 1b: the pairs of each block, sorted. */
    private final List<long[]> blocks = new ArrayList<>();

    /** Phase 1b: block id by scoped content hash. */
    private final LongIntTable intern = new LongIntTable();

    /** Phase 1b: first index entry by scoped pair. */
    private final LongIntTable indexHeads = new LongIntTable();

    private int[] entryBlock = new int[64];

    private int[] entryNext = new int[64];

    private int entries;

    CallBlockProbe(Mode mode, @Nullable Indexer<CSObj> objects) {
        this(mode, objects, Arrays::hashCode);
    }

    CallBlockProbe(Mode mode, @Nullable Indexer<CSObj> objects,
                   ToIntFunction<Object[]> nodesHash) {
        this.mode = mode;
        this.objects = objects;
        this.nodesHash = nodesHash;
    }

    /**
     * @return the probe the option value {@code mode} asks for, null for
     * {@value #NONE}
     */
    static @Nullable CallBlockProbe of(String mode, @Nullable Indexer<CSObj> objects) {
        return switch (mode) {
            case NONE -> null;
            case "p1" -> new CallBlockProbe(Mode.P1, objects);
            case "p1b" -> new CallBlockProbe(Mode.P1B, objects);
            case "p1t" -> new CallBlockProbe(Mode.P1T, objects);
            default -> throw new ConfigException(
                    "call-block-probe must be none, p1, p1b or p1t, not " + mode);
        };
    }

    /** The pairs one event offers at one invoke. */
    public static final class Batch {

        private final CallBlockProbe probe;

        /** The invoke (exact), for the keys of the target hubs. */
        private final Object site;

        /** The hash of the invoke and the class, the scope of phase 1 and 1b. */
        private final long scope;

        private final EdgeClass edgeClass;

        private long[] pairs = new long[8];

        private int size;

        private Object[] fresh = NO_NODES;

        private int freshSize;

        /** The PFG edges of the fresh offers, summed. */
        private long weight;

        /** The argument positions of the hub: the largest argument edges of a fresh offer. */
        private int argPositions;

        /** The result position of the hub: 1 when a fresh offer has return edges. */
        private int resultPosition;

        private Batch(CallBlockProbe probe, Object site, long scope, EdgeClass edgeClass) {
            this.probe = probe;
            this.site = site;
            this.scope = scope;
            this.edgeClass = edgeClass;
        }

        /**
         * Offers the pair of {@code recvObj} (null for a static target) and
         * {@code callee}, without PFG weights.
         *
         * @param unlinked the edge of the pair when the call site's edges do
         *                 not hold it yet, null when they do; the callee is
         *                 fresh when it is not null and not pending from an
         *                 earlier batch
         */
        public void offer(@Nullable CSObj recvObj, CSMethod callee,
                          @Nullable Edge<CSCallSite, CSMethod> unlinked) {
            offer(recvObj, callee, unlinked, 0, 0);
        }

        /**
         * Offers the pair as {@link #offer(CSObj, CSMethod, Edge)} does, with
         * the PFG edges its edge gets when the solver takes it.
         *
         * @param argEdges    the parameter-passing edges of the edge
         * @param returnEdges the return edges of the edge
         */
        public void offer(@Nullable CSObj recvObj, CSMethod callee,
                          @Nullable Edge<CSCallSite, CSMethod> unlinked,
                          int argEdges, int returnEdges) {
            int obj = recvObj == null ? -1 : Objects.requireNonNull(probe.objects,
                    "a probe without an object indexer").getIndex(recvObj);
            boolean isFresh = unlinked != null && probe.pending.add(unlinked);
            offer(obj, System.identityHashCode(callee), isFresh ? callee : null,
                    argEdges, returnEdges);
        }

        /** Offers a pair without PFG weights (tests). */
        void offer(int obj, int callee, @Nullable Object freshNode) {
            offer(obj, callee, freshNode, 0, 0);
        }

        /**
         * Offers the pair of object index {@code obj} and callee key
         * {@code callee}; {@code freshNode} is the callee node when it is
         * fresh, else null. The weights count only for a fresh node, which
         * the pending edges make fresh at most once per batch.
         */
        void offer(int obj, int callee, @Nullable Object freshNode,
                   int argEdges, int returnEdges) {
            if (size == pairs.length) {
                pairs = Arrays.copyOf(pairs, size * 2);
            }
            pairs[size++] = ((long) obj << 32) | (callee & 0xffffffffL);
            if (freshNode != null) {
                if (freshSize == fresh.length) {
                    fresh = Arrays.copyOf(fresh, Math.max(4, freshSize * 2));
                }
                fresh[freshSize++] = freshNode;
                weight += argEdges + returnEdges;
                argPositions = Math.max(argPositions, argEdges);
                if (returnEdges > 0) {
                    resultPosition = 1;
                }
            }
        }
    }

    /** @return a new batch of {@code edgeClass} at {@code callSite} */
    public Batch begin(Invoke callSite, EdgeClass edgeClass) {
        long site = ((long) System.identityHashCode(callSite) << 32)
                | (System.identityHashCode(callSite.getContainer()) & 0xffffffffL);
        return begin(callSite, site, edgeClass);
    }

    Batch begin(Object site, long siteHash, EdgeClass edgeClass) {
        return new Batch(this, site, mix(siteHash + edgeClass.ordinal() * 0x9E3779B97F4A7C15L),
                edgeClass);
    }

    /** Counts {@code batch}; a batch without pairs counts nothing. */
    public void end(Batch batch) {
        if (batch.size == 0) {
            return;
        }
        long[] pairs = Arrays.copyOf(batch.pairs, batch.size);
        Arrays.sort(pairs);
        pairs = distinct(pairs);
        int n = pairs.length;
        int targets = distinctTargets(pairs);
        Object[] freshNodes = distinctNodes(batch.fresh, batch.freshSize);
        int fresh = freshNodes.length;
        int base = batch.edgeClass.ordinal() * COUNTERS;
        add(base, Counter.BATCHES, 1);
        add(base, Counter.OFFERS, n);
        add(base, Counter.DIRECT, targets);
        add(base, Counter.FRESH, fresh);
        if (fresh == 0) {
            add(base, Counter.STALE, 1);
        }
        add(base, Counter.W_TODAY, batch.weight);
        if (mode != Mode.P1T) {
            long hash = contentHash(batch.scope, pairs);
            countPhase1(base, n, targets, fresh, hash);
            if (mode == Mode.P1B) {
                countPhase1b(base, batch.scope, pairs, hash, targets, fresh);
            }
        }
        countTargetHubs(base, batch, freshNodes);
    }

    private void countPhase1(int base, int n, int targets, int fresh, long hash) {
        if (n == 1) {
            add(base, Counter.P1_SINGLES, 1);
            add(base, Counter.P1_SINGLE_FRESH, fresh);
        }
        if (phase1Blocks.get(hash) < 0) {
            phase1Blocks.put(hash, 1);
            add(base, Counter.P1_BLOCKS, 1);
            add(base, Counter.P1_BLOCK_PAIRS, n);
            add(base, Counter.P1_BLOCK_TARGETS, targets);
            if (n == 1) {
                add(base, Counter.P1_SINGLE_MISSES, 1);
            }
        } else {
            add(base, Counter.P1_HITS, 1);
        }
    }

    private void countPhase1b(int base, long scope, long[] pairs, long hash,
                              int targets, int fresh) {
        int n = pairs.length;
        if (n == 1) {
            // rule 4: a batch of one pair is never kept, so it costs its edge
            add(base, Counter.P1B_COST, fresh);
            return;
        }
        if (equalBlock(hash, pairs)) {
            add(base, Counter.P1B_HITS, 1);
            add(base, Counter.P1B_COST, 1);
            return;
        }
        boolean[] taken = new boolean[n];
        int pieces = 0;
        int covered = 0;
        for (int id : candidates(scope, pairs)) {
            long[] block = blocks.get(id);
            if (block.length <= n - covered && fits(block, pairs, taken)) {
                for (long pair : block) {
                    taken[Arrays.binarySearch(pairs, pair)] = true;
                }
                ++pieces;
                covered += block.length;
            }
        }
        if (pieces == 0) {
            register(base, scope, pairs, hash);
            add(base, Counter.P1B_BLOCK_TARGETS, targets);
            add(base, Counter.P1B_COST, 1 + targets);
            return;
        }
        long[] rest = new long[n - covered];
        for (int i = 0, j = 0; i < n; ++i) {
            if (!taken[i]) {
                rest[j++] = pairs[i];
            }
        }
        long restHash = contentHash(scope, rest);
        int restTargets = distinctTargets(rest);
        boolean newRest = rest.length >= 2 && !equalBlock(restHash, rest);
        long restCost = rest.length == 0 ? 0
                : rest.length == 1 || !newRest ? 1 : 1 + restTargets;
        long cost = pieces + restCost;
        if (cost > targets) {
            add(base, Counter.P1B_FALLBACKS, 1);
            add(base, Counter.P1B_COST, targets);
            return;
        }
        add(base, Counter.P1B_COVERED, 1);
        add(base, Counter.P1B_PIECES, pieces);
        add(base, Counter.P1B_COST, cost);
        if (newRest) {
            register(base, scope, rest, restHash);
            add(base, Counter.P1B_BLOCK_TARGETS, restTargets);
        }
    }

    private void countTargetHubs(int base, Batch batch, Object[] freshNodes) {
        int fresh = freshNodes.length;
        if (fresh == 0) {
            return;
        }
        if (fresh == 1) {
            add(base, Counter.P1T_SINGLES, 1);
            add(base, Counter.P1T_COST, 1);
            add(base, Counter.W_DIRECT, batch.weight);
            return;
        }
        int positions = batch.argPositions + batch.resultPosition;
        add(base, Counter.P1T_REFS, 1);
        add(base, Counter.W_JOIN, positions);
        int hash = 31 * (31 * batch.site.hashCode() + batch.edgeClass.ordinal())
                + nodesHash.applyAsInt(freshNodes);
        TargetKey key = new TargetKey(batch.site, batch.edgeClass, freshNodes, hash, positions);
        TargetKey known = targetKeys.putIfAbsent(key, key);
        if (known == null) {
            add(base, Counter.P1T_HUBS, 1);
            add(base, Counter.P1T_HUB1, 1);
            add(base, Counter.P1T_TARGETS, fresh);
            add(base, Counter.P1T_COST, 1 + fresh);
            add(base, Counter.W_TARGETS, batch.weight);
            add(base, Counter.W_JOIN1, positions);
        } else {
            add(base, Counter.P1T_HITS, 1);
            add(base, Counter.P1T_COST, 1);
            if (++known.members == 2) {
                add(base, Counter.P1T_HUB1, -1);
                add(base, Counter.P1T_HUB2, 1);
                add(base, Counter.HUB_PTRS2, known.positions);
            }
        }
    }

    /**
     * The key of a target hub: an invoke, an edge class and a set of callee
     * nodes sorted by hash code. Equal only when all three are equal.
     */
    private static final class TargetKey {

        private final Object site;

        private final EdgeClass edgeClass;

        private final Object[] nodes;

        private final int hash;

        /** The hub positions (arguments and result) of the first member. */
        private final int positions;

        /** The batches that made or hit this key. */
        private int members = 1;

        private TargetKey(Object site, EdgeClass edgeClass, Object[] nodes, int hash,
                          int positions) {
            this.site = site;
            this.edgeClass = edgeClass;
            this.nodes = nodes;
            this.hash = hash;
            this.positions = positions;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof TargetKey that)) {
                return false;
            }
            return hash == that.hash && edgeClass == that.edgeClass
                    && site.equals(that.site) && sameNodes(nodes, that.nodes);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** @return whether the distinct, hash-sorted node sets {@code a} and {@code b} are equal */
    private static boolean sameNodes(Object[] a, Object[] b) {
        if (a.length != b.length) {
            return false;
        }
        for (Object node : a) {
            if (!containsNode(b, node)) {
                return false;
            }
        }
        return true;
    }

    /** @return whether the hash-sorted {@code nodes} hold {@code node} */
    private static boolean containsNode(Object[] nodes, Object node) {
        int h = node.hashCode();
        int lo = 0;
        int hi = nodes.length;
        while (lo < hi) {
            int mid = (lo + hi) >>> 1;
            if (nodes[mid].hashCode() < h) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        for (int i = lo; i < nodes.length && nodes[i].hashCode() == h; ++i) {
            if (nodes[i].equals(node)) {
                return true;
            }
        }
        return false;
    }

    /** @return the distinct nodes of the first {@code size} of {@code nodes}, sorted by hash code */
    private static Object[] distinctNodes(Object[] nodes, int size) {
        if (size == 0) {
            return NO_NODES;
        }
        Object[] sorted = Arrays.copyOf(nodes, size);
        Arrays.sort(sorted, BY_HASH);
        int n = 0;
        for (int i = 0; i < size; ++i) {
            Object node = sorted[i];
            boolean seen = false;
            // equal nodes have equal hash codes, so a duplicate is in the run
            for (int j = n - 1; j >= 0 && sorted[j].hashCode() == node.hashCode(); --j) {
                if (sorted[j].equals(node)) {
                    seen = true;
                    break;
                }
            }
            if (!seen) {
                sorted[n++] = node;
            }
        }
        return n == size ? sorted : Arrays.copyOf(sorted, n);
    }

    private boolean equalBlock(long hash, long[] pairs) {
        int id = intern.get(hash);
        return id >= 0 && Arrays.equals(blocks.get(id), pairs);
    }

    /** @return the blocks of {@code scope} sharing a pair with {@code pairs}, larger first */
    private List<Integer> candidates(long scope, long[] pairs) {
        Set<Integer> seen = new HashSet<>();
        List<Integer> found = new ArrayList<>();
        for (long pair : pairs) {
            // at most CHAIN_LIMIT blocks per pair, newest first, so a pair in
            // many blocks does not make the scan quadratic (a cover may then
            // miss an older block: the cost is an upper bound)
            int seenInChain = 0;
            for (int e = indexHeads.get(mix(scope ^ pair));
                 e >= 0 && seenInChain < CHAIN_LIMIT; e = entryNext[e], ++seenInChain) {
                if (seen.add(entryBlock[e])) {
                    found.add(entryBlock[e]);
                }
            }
        }
        found.sort(Comparator.<Integer>comparingInt(id -> -blocks.get(id).length)
                .thenComparingInt(id -> id));
        return found;
    }

    private static boolean fits(long[] block, long[] pairs, boolean[] taken) {
        for (long pair : block) {
            int i = Arrays.binarySearch(pairs, pair);
            if (i < 0 || taken[i]) {
                return false;
            }
        }
        return true;
    }

    private void register(int base, long scope, long[] pairs, long hash) {
        int id = blocks.size();
        blocks.add(pairs);
        intern.put(hash, id);
        add(base, Counter.P1B_BLOCKS, 1);
        add(base, Counter.P1B_BLOCK_PAIRS, pairs.length);
        for (long pair : pairs) {
            long key = mix(scope ^ pair);
            if (entries == entryBlock.length) {
                entryBlock = Arrays.copyOf(entryBlock, entries * 2);
                entryNext = Arrays.copyOf(entryNext, entries * 2);
            }
            entryBlock[entries] = id;
            entryNext[entries] = indexHeads.get(key);
            indexHeads.put(key, entries);
            ++entries;
        }
    }

    /**
     * Notes that the solver polled {@code edge} from its work list: from now
     * on the call graph tells whether it is linked.
     */
    void edgePolled(Edge<CSCallSite, CSMethod> edge) {
        pending.remove(edge);
    }

    /**
     * Counts an edge the call graph took: a {@link Classified} edge by its
     * class, a plain virtual, interface or special edge as {@link
     * EdgeClass#PLAIN}, any other edge not at all.
     */
    void edgeAdded(Edge<CSCallSite, CSMethod> edge) {
        EdgeClass edgeClass;
        if (edge instanceof Classified classified) {
            edgeClass = classified.blockProbeClass();
        } else if (edge.getClass() == Edge.class && (edge.getKind() == CallKind.VIRTUAL
                || edge.getKind() == CallKind.INTERFACE || edge.getKind() == CallKind.SPECIAL)) {
            edgeClass = EdgeClass.PLAIN;
        } else {
            return;
        }
        add(edgeClass.ordinal() * COUNTERS, Counter.EDGES, 1);
    }

    /** @return the counter {@code counter} of {@code edgeClass} */
    public long count(EdgeClass edgeClass, Counter counter) {
        return counts[edgeClass.ordinal() * COUNTERS + counter.ordinal()];
    }

    /** @return the phase-1 cost of {@code edgeClass}: hub references plus target edges */
    public long phase1Cost(EdgeClass edgeClass) {
        return count(edgeClass, Counter.BATCHES) + count(edgeClass, Counter.P1_BLOCK_TARGETS);
    }

    /**
     * @return the phase-1 cost of {@code edgeClass} with rule 4: a batch of
     * one pair costs its fresh edges, any other batch one hub reference plus,
     * for a new block, its target edges
     */
    public long phase1RuleCost(EdgeClass edgeClass) {
        return count(edgeClass, Counter.BATCHES) - count(edgeClass, Counter.P1_SINGLES)
                + count(edgeClass, Counter.P1_BLOCK_TARGETS)
                - count(edgeClass, Counter.P1_SINGLE_MISSES)
                + count(edgeClass, Counter.P1_SINGLE_FRESH);
    }

    /** @return the pairs a phase-1 design keeps: those of the new blocks of two or more pairs */
    public long phase1StoredPairs(EdgeClass edgeClass) {
        return count(edgeClass, Counter.P1_BLOCK_PAIRS) - count(edgeClass, Counter.P1_SINGLE_MISSES);
    }

    /** @return whether phase 1b is simulated (mode {@code p1b}) */
    public boolean simulatesPhase1b() {
        return mode == Mode.P1B;
    }

    /** @return whether phase 1 is simulated (modes {@code p1} and {@code p1b}) */
    public boolean simulatesPhase1() {
        return mode != Mode.P1T;
    }

    /** @return the counters as one log line, per edge class and in total */
    public String line() {
        StringBuilder line = new StringBuilder(mode.name().toLowerCase());
        long[] total = new long[5];
        for (EdgeClass c : EdgeClass.values()) {
            line.append("; ").append(c.name().toLowerCase())
                    .append(" edges=").append(count(c, Counter.EDGES));
            total[0] += count(c, Counter.EDGES);
            if (!isHubbable(c)) {
                // reflective, static and constructor targets stay direct
                continue;
            }
            line.append(" t_batches=").append(count(c, Counter.BATCHES))
                    .append(" offers=").append(count(c, Counter.OFFERS))
                    .append(" direct=").append(count(c, Counter.DIRECT))
                    .append(" t_fresh=").append(count(c, Counter.FRESH))
                    .append(" t_stale=").append(count(c, Counter.STALE))
                    .append(" t_single=").append(count(c, Counter.P1T_SINGLES))
                    .append(" t_multi=").append(count(c, Counter.P1T_REFS))
                    .append(" t_hits=").append(count(c, Counter.P1T_HITS))
                    .append(" t_hubs=").append(count(c, Counter.P1T_HUBS))
                    .append(" t_targets=").append(count(c, Counter.P1T_TARGETS))
                    .append(" t_hub1=").append(count(c, Counter.P1T_HUB1))
                    .append(" t_hub2=").append(count(c, Counter.P1T_HUB2))
                    .append(" p1t=").append(count(c, Counter.P1T_COST))
                    .append(" w_today=").append(count(c, Counter.W_TODAY))
                    .append(" w_direct=").append(count(c, Counter.W_DIRECT))
                    .append(" w_targets=").append(count(c, Counter.W_TARGETS))
                    .append(" w_join=").append(count(c, Counter.W_JOIN))
                    .append(" w_join1=").append(count(c, Counter.W_JOIN1))
                    .append(" hub_ptrs=").append(count(c, Counter.W_JOIN1))
                    .append(" hub_ptrs2=").append(count(c, Counter.HUB_PTRS2));
            total[1] += count(c, Counter.FRESH);
            total[2] += count(c, Counter.P1T_COST);
            total[3] += count(c, Counter.W_TODAY);
            if (simulatesPhase1()) {
                line.append(" p1=").append(phase1Cost(c))
                        .append(" (hits=").append(count(c, Counter.P1_HITS))
                        .append(" blocks=").append(count(c, Counter.P1_BLOCKS))
                        .append(" pairs=").append(count(c, Counter.P1_BLOCK_PAIRS))
                        .append(" targets=").append(count(c, Counter.P1_BLOCK_TARGETS))
                        .append(" singles=").append(count(c, Counter.P1_SINGLES))
                        .append(" single_fresh=").append(count(c, Counter.P1_SINGLE_FRESH))
                        .append(") p1r=").append(phase1RuleCost(c))
                        .append(" stored_pairs=").append(phase1StoredPairs(c));
            }
            if (simulatesPhase1b()) {
                line.append(" p1b=").append(count(c, Counter.P1B_COST))
                        .append(" (hits=").append(count(c, Counter.P1B_HITS))
                        .append(" covered=").append(count(c, Counter.P1B_COVERED))
                        .append(" pieces=").append(count(c, Counter.P1B_PIECES))
                        .append(" blocks=").append(count(c, Counter.P1B_BLOCKS))
                        .append(" pairs=").append(count(c, Counter.P1B_BLOCK_PAIRS))
                        .append(" targets=").append(count(c, Counter.P1B_BLOCK_TARGETS))
                        .append(" fallbacks=").append(count(c, Counter.P1B_FALLBACKS))
                        .append(')');
            }
            total[4] += phase1RuleCost(c);
        }
        line.append("; total edges=").append(total[0]).append(" t_fresh=").append(total[1])
                .append(" p1t=").append(total[2]).append(" w_today=").append(total[3]);
        if (simulatesPhase1()) {
            line.append(" p1r=").append(total[4]);
        }
        return line.toString();
    }

    /**
     * @return whether the line shows the hub counters of {@code edgeClass}:
     * plain calls and lambda instance targets; the design keeps the other
     * classes direct, so the line shows only their edges
     */
    private static boolean isHubbable(EdgeClass edgeClass) {
        return edgeClass == EdgeClass.PLAIN || edgeClass == EdgeClass.LAMBDA_BOUND
                || edgeClass == EdgeClass.LAMBDA_UNBOUND;
    }

    private void add(int base, Counter counter, long delta) {
        counts[base + counter.ordinal()] += delta;
    }

    /** @return the distinct elements of the sorted {@code pairs} */
    private static long[] distinct(long[] pairs) {
        int n = 0;
        for (int i = 0; i < pairs.length; ++i) {
            if (i == 0 || pairs[i] != pairs[i - 1]) {
                pairs[n++] = pairs[i];
            }
        }
        return n == pairs.length ? pairs : Arrays.copyOf(pairs, n);
    }

    private static int distinctTargets(long[] pairs) {
        int[] callees = new int[pairs.length];
        for (int i = 0; i < pairs.length; ++i) {
            callees[i] = (int) pairs[i];
        }
        Arrays.sort(callees);
        int n = 0;
        for (int i = 0; i < callees.length; ++i) {
            if (i == 0 || callees[i] != callees[i - 1]) {
                ++n;
            }
        }
        return n;
    }

    private static long contentHash(long scope, long[] pairs) {
        long h = scope;
        for (long pair : pairs) {
            h = mix(h ^ pair);
        }
        return mix(h + pairs.length);
    }

    /** The finalizer of SplitMix64. */
    private static long mix(long x) {
        long z = x + 0x9E3779B97F4A7C15L;
        z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
        z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
        return z ^ (z >>> 31);
    }

    /** An open-addressing map from long to non-negative int. */
    private static final class LongIntTable {

        private long[] keys = new long[16];

        /** The value plus one; 0 marks a free slot. */
        private int[] values = new int[16];

        private int size;

        /** @return the value of {@code key}, -1 when absent */
        int get(long key) {
            int mask = keys.length - 1;
            for (int i = slot(key, mask); values[i] != 0; i = (i + 1) & mask) {
                if (keys[i] == key) {
                    return values[i] - 1;
                }
            }
            return -1;
        }

        void put(long key, int value) {
            if (2 * (size + 1) > keys.length) {
                grow();
            }
            int mask = keys.length - 1;
            int i = slot(key, mask);
            while (values[i] != 0 && keys[i] != key) {
                i = (i + 1) & mask;
            }
            if (values[i] == 0) {
                ++size;
            }
            keys[i] = key;
            values[i] = value + 1;
        }

        private void grow() {
            long[] oldKeys = keys;
            int[] oldValues = values;
            keys = new long[oldKeys.length * 2];
            values = new int[oldValues.length * 2];
            size = 0;
            for (int i = 0; i < oldKeys.length; ++i) {
                if (oldValues[i] != 0) {
                    put(oldKeys[i], oldValues[i] - 1);
                }
            }
        }

        private static int slot(long key, int mask) {
            return (int) mix(key) & mask;
        }
    }
}
