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
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * The block-sharing probe of the call hub design (option
 * {@code call-block-probe}, px/s116 step L0). It only counts: it adds no
 * pointer, edge or context and changes no order.
 * <p>
 * A <em>batch</em> is what one event of an edge source offers at one invoke:
 * the receiver diff of {@link DefaultSolver}'s processCall at one call site,
 * one receiver grouping of the lambda analysis, one reflective edge. Its
 * content is the set of pairs (receiver object, callee node) it offers. The
 * probe simulates the hub blocks of the design on these contents, per invoke
 * and edge class:
 * <ul>
 * <li>phase 1: a batch whose content equals an earlier block of the invoke
 * joins it (one hub reference), otherwise it makes a new block (one hub
 * reference plus one target edge per distinct callee node);</li>
 * <li>phase 1 with rule 4: a new one-pair block costs one direct edge and is
 * not kept;</li>
 * <li>phase 1b (mode {@code p1b}): a miss of two or more pairs is covered by
 * earlier whole blocks of the invoke that are subsets of it (greedy by size,
 * disjoint) plus one remainder block; a cover dearer than the direct edges
 * falls back to them.</li>
 * </ul>
 * The direct cost of a batch is its number of distinct callee nodes, the
 * edges it makes without hubs when none of them exists yet; {@link
 * Counter#EDGES} counts the call edges the call graph actually took.
 * Callee nodes are told apart by identity hash code (a collision with the
 * same receiver object at the same invoke would merge two pairs), contents
 * of phase 1 by a 64-bit hash.
 */
public final class CallBlockProbe {

    /** The option value that turns the probe off (the default). */
    static final String NONE = "none";

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
        P1_HITS,
        P1_BLOCKS,
        P1_BLOCK_PAIRS,
        P1_BLOCK_TARGETS,
        /** Phase-1 misses of one pair (rule 4 makes them direct). */
        P1_SINGLE_MISSES,
        P1B_HITS,
        /** Misses covered by at least one earlier block. */
        P1B_COVERED,
        /** Earlier blocks used in covers. */
        P1B_PIECES,
        P1B_BLOCKS,
        P1B_BLOCK_TARGETS,
        P1B_FALLBACKS,
        /** Phase-1b cost: hub references, target edges and direct edges. */
        P1B_COST
    }

    /** The blocks per pair that a phase-1b cover looks at. */
    private static final int CHAIN_LIMIT = 64;

    private static final int CLASSES = EdgeClass.values().length;

    private static final int COUNTERS = Counter.values().length;

    private final boolean phase1b;

    private final @Nullable Indexer<CSObj> objects;

    private final long[] counts = new long[CLASSES * COUNTERS];

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

    CallBlockProbe(boolean phase1b, @Nullable Indexer<CSObj> objects) {
        this.phase1b = phase1b;
        this.objects = objects;
    }

    /**
     * @return the probe the option value {@code mode} asks for, null for
     * {@value #NONE}
     */
    static @Nullable CallBlockProbe of(String mode, @Nullable Indexer<CSObj> objects) {
        return switch (mode) {
            case NONE -> null;
            case "p1" -> new CallBlockProbe(false, objects);
            case "p1b" -> new CallBlockProbe(true, objects);
            default -> throw new ConfigException(
                    "call-block-probe must be none, p1 or p1b, not " + mode);
        };
    }

    /** The pairs one event offers at one invoke. */
    public static final class Batch {

        private final long scope;

        private final EdgeClass edgeClass;

        private final @Nullable Indexer<CSObj> objects;

        private long[] pairs = new long[8];

        private int size;

        private Batch(long scope, EdgeClass edgeClass, @Nullable Indexer<CSObj> objects) {
            this.scope = scope;
            this.edgeClass = edgeClass;
            this.objects = objects;
        }

        /**
         * Offers the pair of {@code recvObj} (null for a static target) and
         * {@code callee}.
         */
        public void offer(@Nullable CSObj recvObj, CSMethod callee) {
            int obj = recvObj == null ? -1 : Objects.requireNonNull(objects,
                    "a probe without an object indexer").getIndex(recvObj);
            offer(obj, System.identityHashCode(callee));
        }

        void offer(int obj, int callee) {
            if (size == pairs.length) {
                pairs = Arrays.copyOf(pairs, size * 2);
            }
            pairs[size++] = ((long) obj << 32) | (callee & 0xffffffffL);
        }
    }

    /** @return a new batch of {@code edgeClass} at {@code callSite} */
    public Batch begin(Invoke callSite, EdgeClass edgeClass) {
        long site = ((long) System.identityHashCode(callSite) << 32)
                | (System.identityHashCode(callSite.getContainer()) & 0xffffffffL);
        return begin(site, edgeClass);
    }

    Batch begin(long site, EdgeClass edgeClass) {
        return new Batch(mix(site + edgeClass.ordinal() * 0x9E3779B97F4A7C15L),
                edgeClass, objects);
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
        long hash = contentHash(batch.scope, pairs);
        int base = batch.edgeClass.ordinal() * COUNTERS;
        add(base, Counter.BATCHES, 1);
        add(base, Counter.OFFERS, n);
        add(base, Counter.DIRECT, targets);
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
        if (phase1b) {
            countPhase1b(base, batch.scope, pairs, hash, targets);
        }
    }

    private void countPhase1b(int base, long scope, long[] pairs, long hash, int targets) {
        if (equalBlock(hash, pairs)) {
            add(base, Counter.P1B_HITS, 1);
            add(base, Counter.P1B_COST, 1);
            return;
        }
        int n = pairs.length;
        if (n == 1) {
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
            register(scope, pairs, hash);
            add(base, Counter.P1B_BLOCKS, 1);
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
            register(scope, rest, restHash);
            add(base, Counter.P1B_BLOCKS, 1);
            add(base, Counter.P1B_BLOCK_TARGETS, restTargets);
        }
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

    private void register(long scope, long[] pairs, long hash) {
        int id = blocks.size();
        blocks.add(pairs);
        intern.put(hash, id);
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

    /** @return the phase-1 cost of {@code edgeClass} with rule 4 */
    public long phase1RuleCost(EdgeClass edgeClass) {
        return phase1Cost(edgeClass) - count(edgeClass, Counter.P1_SINGLE_MISSES);
    }

    /** @return whether phase 1b is simulated (mode {@code p1b}) */
    public boolean simulatesPhase1b() {
        return phase1b;
    }

    /** @return the counters as one log line, per edge class and in total */
    public String line() {
        StringBuilder line = new StringBuilder(phase1b ? "p1b" : "p1");
        long edges = 0;
        long direct = 0;
        long p1 = 0;
        long p1r = 0;
        long p1b = 0;
        for (EdgeClass c : EdgeClass.values()) {
            line.append("; ").append(c.name().toLowerCase())
                    .append(" batches=").append(count(c, Counter.BATCHES))
                    .append(" offers=").append(count(c, Counter.OFFERS))
                    .append(" direct=").append(count(c, Counter.DIRECT))
                    .append(" edges=").append(count(c, Counter.EDGES))
                    .append(" p1=").append(phase1Cost(c))
                    .append(" (hits=").append(count(c, Counter.P1_HITS))
                    .append(" blocks=").append(count(c, Counter.P1_BLOCKS))
                    .append(" pairs=").append(count(c, Counter.P1_BLOCK_PAIRS))
                    .append(" targets=").append(count(c, Counter.P1_BLOCK_TARGETS))
                    .append(") p1r=").append(phase1RuleCost(c));
            if (phase1b) {
                line.append(" p1b=").append(count(c, Counter.P1B_COST))
                        .append(" (hits=").append(count(c, Counter.P1B_HITS))
                        .append(" covered=").append(count(c, Counter.P1B_COVERED))
                        .append(" pieces=").append(count(c, Counter.P1B_PIECES))
                        .append(" blocks=").append(count(c, Counter.P1B_BLOCKS))
                        .append(" targets=").append(count(c, Counter.P1B_BLOCK_TARGETS))
                        .append(" fallbacks=").append(count(c, Counter.P1B_FALLBACKS))
                        .append(')');
            }
            edges += count(c, Counter.EDGES);
            direct += count(c, Counter.DIRECT);
            p1 += phase1Cost(c);
            p1r += phase1RuleCost(c);
            p1b += count(c, Counter.P1B_COST);
        }
        line.append("; total edges=").append(edges).append(" direct=").append(direct)
                .append(" p1=").append(p1).append(" p1r=").append(p1r);
        if (phase1b) {
            line.append(" p1b=").append(p1b);
        }
        return line.toString();
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
