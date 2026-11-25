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
import pascal.taie.World;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.pts.DelegatePointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.AbstractHybridSet;
import pascal.taie.util.collection.GenericBitSet;
import pascal.taie.util.collection.IndexerBitSet;
import pascal.taie.util.collection.SparseBitSet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.IntPredicate;
import java.util.function.Supplier;

/**
 * Transfer function that filters out the objects whose types are NOT
 * subtypes of specific type.
 * <p>
 * The result is the objects of the input whose type is assignable to the
 * guard type, in a points-to set of the same representation (singleton,
 * small set up to the hybrid threshold, bit set above it) and the same
 * iteration order as inserting them one by one. The test of an object goes
 * through a memo per guard type over dense ids of the objects' types
 * (objects of one type share the answer), so the type system is asked at
 * most once per (guard type, object type). For inputs held in bit sets the
 * memo also holds the objects that passed (pass), a bit set over the
 * solver's object index, filled in index order up to a watermark: every
 * index below it is checked except the holes, the indexes that held no
 * object when the watermark went past them (an indexer may give a later
 * object a free lower index). Such an input is filtered word by word: the
 * watermark first moves up to its highest index, checking each index on
 * the way by its type id, read from a flat array (the object itself is
 * read only the first time its type id is assigned); then in one pass over
 * its words only its bits in the holes are checked, and the bits of input
 * AND pass are counted; the result is the input AND pass (the input itself
 * if all pass). A smaller input is filtered object by object through the
 * type memo. The memos of the
 * last solver are kept until the next solver replaces them or the world is
 * reset (a pointer analysis run as an analysis of the world keeps its
 * result there until then anyway). The
 * solver and the points-to sets it creates must share the object indexer
 * (as DefaultSolver does): bit sets over different indexers cannot be
 * combined.
 * <p>
 * {@code -Dspd.typefilter.verify=true} recomputes every application with
 * the original per-object filter and fails on any difference of contents,
 * iteration order or representation; the count is printed at JVM exit.
 */
public class TypeFilter implements Transfer {

    private static final boolean VERIFY = Boolean.getBoolean("spd.typefilter.verify");

    private static final AtomicLong VERIFIED = new AtomicLong();

    private static final boolean STATS = Boolean.getBoolean("spd.typefilter.stats");

    private static final AtomicLong STAT_APPLICATIONS = new AtomicLong();

    private static final AtomicLong STAT_LARGE = new AtomicLong();

    private static final AtomicLong STAT_TESTS = new AtomicLong();

    private static final AtomicLong STAT_NANOS = new AtomicLong();

    static {
        World.registerResetCallback(TypeFilter::clearMemos);
        if (VERIFY) {
            Runtime.getRuntime().addShutdownHook(new Thread(() ->
                    System.err.println("[spd] TypeFilter verified applications: " + VERIFIED.get())));
        }
        if (STATS) {
            Runtime.getRuntime().addShutdownHook(new Thread(TypeFilter::printStats));
        }
    }

    /**
     * Dense ids of the types of the objects checked so far, shared by the
     * memos created between two resets. The type of an object is looked up in a
     * map once per object; later reads take its id from a flat array over
     * the object index, without reading the object.
     */
    private static final class ObjectTypes {

        private final Indexer<CSObj> indexer;

        private final Map<Type, Integer> ids = new HashMap<>();

        /**
         * The type of each id.
         */
        private final List<Type> types = new ArrayList<>();

        /**
         * The type id plus one per object index; 0 if not assigned yet.
         */
        private int[] idPlusOne = new int[0];

        ObjectTypes(Indexer<CSObj> indexer) {
            this.indexer = indexer;
        }

        int idOf(CSObj o) {
            int index = indexer.getIndex(o);
            int[] table = idPlusOne;
            if (index < table.length && table[index] != 0) {
                return table[index] - 1;
            }
            return assign(o, index);
        }

        /**
         * @return the type id of the object of the index; the object is read
         * from the indexer only if its id is not assigned yet.
         */
        int idOfIndex(int index) {
            int[] table = idPlusOne;
            if (index < table.length && table[index] != 0) {
                return table[index] - 1;
            }
            return assign(indexer.getObject(index), index);
        }

        /**
         * @return the type id of the object of the index, or -1 if the
         * index holds no object (yet).
         */
        int idOfIndexOrMissing(int index) {
            int[] table = idPlusOne;
            if (index < table.length && table[index] != 0) {
                return table[index] - 1;
            }
            CSObj o = indexer.getObject(index);
            return o == null ? -1 : assign(o, index);
        }

        Type typeOf(int id) {
            return types.get(id);
        }

        private int assign(CSObj o, int index) {
            Type type = o.getObject().getType();
            Integer id = ids.get(type);
            if (id == null) {
                id = ids.size();
                ids.put(type, id);
                types.add(type);
            }
            if (index >= idPlusOne.length) {
                idPlusOne = Arrays.copyOf(idPlusOne, Math.max(index + 1, 2 * idPlusOne.length));
            }
            idPlusOne[index] = id + 1;
            return id;
        }
    }

    /**
     * Memo of one guard type: the object indexes already checked, and the
     * objects that passed; and per object type id (see {@link ObjectTypes})
     * the types already checked, and those that passed. The checked
     * indexes are those below {@link #watermark} except the {@link #holes}.
     */
    private static final class Memo {

        final IndexerBitSet<CSObj> pass;

        final ObjectTypes types;

        /**
         * Every index below it is checked, except the holes.
         */
        int watermark;

        /**
         * The indexes below {@link #watermark} that held no object when the
         * watermark went past them, and have not been checked since (an
         * indexer may give a later object a free lower index), a word per
         * 64 indexes from index 0.
         */
        long[] holes = new long[0];

        private long[] typeKnown = new long[0];

        private long[] typePass = new long[0];

        Memo(Indexer<CSObj> indexer, ObjectTypes types) {
            pass = new IndexerBitSet<>(indexer, true);
            this.types = types;
        }

        void addHole(int index) {
            int word = index >>> 6;
            if (word >= holes.length) {
                holes = Arrays.copyOf(holes, Math.max(word + 1, 2 * holes.length));
            }
            holes[word] |= 1L << index;
        }

        /**
         * @return 1 if the objects of the type pass, 0 if they fail, -1 if
         * the type was not checked yet.
         */
        int typeResult(int typeId) {
            int word = typeId >>> 6;
            long bit = 1L << typeId;
            if (word >= typeKnown.length || (typeKnown[word] & bit) == 0) {
                return -1;
            }
            return (typePass[word] & bit) != 0 ? 1 : 0;
        }

        void recordType(int typeId, boolean passes) {
            int word = typeId >>> 6;
            if (word >= typeKnown.length) {
                int length = Math.max(word + 1, 2 * typeKnown.length);
                typeKnown = Arrays.copyOf(typeKnown, length);
                typePass = Arrays.copyOf(typePass, length);
            }
            long bit = 1L << typeId;
            typeKnown[word] |= bit;
            if (passes) {
                typePass[word] |= bit;
            }
        }
    }

    private static @Nullable Indexer<CSObj> memoIndexer;

    private static @Nullable ObjectTypes objectTypes;

    private static Map<Type, Memo> memos = new HashMap<>();

    /**
     * The guard type.
     */
    private final Type type;

    private final TypeSystem typeSystem;

    private final Supplier<PointsToSet> ptsFactory;

    private final Indexer<CSObj> indexer;

    /**
     * {@link #checkIndexWithMemo} as a predicate on object indexes, created
     * once per filter.
     */
    private final IntPredicate checker = this::checkIndexWithMemo;

    private @Nullable Memo memo;

    private long applications;

    /**
     * The objects or object indexes this filter checked so far, counted
     * only with {@code -Dspd.typefilter.stats=true}.
     */
    private long tests;

    /**
     * The delta that a solver is propagating and the result of this filter
     * on it, or null outside a propagation that applied it; set and cleared
     * by {@link DeltaTransfers}.
     */
    @Nullable PointsToSet deltaInput;

    @Nullable PointsToSet deltaResult;

    /**
     * The kind and the transfer of a pointer flow edge whose only transfer
     * is a type filter, in one object, so that an out-edge store without
     * edge objects keeps them in one slot (see {@link #edgeTag(FlowKind)}).
     * Internal to the out-edge store of the pointers; public only because
     * that store is in another package.
     *
     * @param filter the only transfer of the edge
     * @param kind   the kind of the edge
     */
    public record EdgeTag(TypeFilter filter, FlowKind kind) {
    }

    private static final int FLOW_KINDS = FlowKind.values().length;

    /**
     * The tag of the first {@link FlowKind} asked for, or null before;
     * most filters only ever serve one kind.
     */
    private @Nullable EdgeTag firstEdgeTag;

    /**
     * The tags of the other kinds, by ordinal, or null until a second
     * kind is asked for.
     */
    private @Nullable EdgeTag @Nullable [] edgeTags;

    public TypeFilter(Type type, Solver solver) {
        this.type = type;
        this.typeSystem = solver.getTypeSystem();
        this.ptsFactory = solver::makePointsToSet;
        this.indexer = solver.getCSManager().getObjectIndexer();
    }

    private static synchronized Memo memoFor(Type type, Indexer<CSObj> indexer) {
        ObjectTypes types = objectTypes;
        if (memoIndexer != indexer || types == null) {
            memoIndexer = indexer;
            types = new ObjectTypes(indexer);
            objectTypes = types;
            memos = new HashMap<>();
        }
        ObjectTypes shared = types;
        return memos.computeIfAbsent(type, t -> new Memo(indexer, shared));
    }

    /**
     * Drops the memos (and with them the last solver's objects) when the
     * world is reset, or when a solver releases its state after its fixed
     * point (the memos only cache {@link #passes}; a later application
     * builds them again).
     */
    static synchronized void clearMemos() {
        if (STATS && !memos.isEmpty()) {
            printStats();
        }
        memoIndexer = null;
        objectTypes = null;
        memos = new HashMap<>();
    }

    /**
     * Drops this filter's reference to its memo, see {@link #clearMemos()}.
     */
    void releaseMemo() {
        memo = null;
    }

    /**
     * @return the number of applications of this filter so far.
     */
    long applications() {
        return applications;
    }

    /**
     * @return the tag of this filter and the kind, the same object for
     * every call with the same kind (the edges of a solver are added by
     * one thread; two threads racing on the first use of a kind would each
     * get a tag of equal content). Internal to the out-edge store of the
     * pointers.
     */
    public EdgeTag edgeTag(FlowKind kind) {
        EdgeTag first = firstEdgeTag;
        if (first != null && first.kind() == kind) {
            return first;
        }
        if (first == null) {
            first = new EdgeTag(this, kind);
            firstEdgeTag = first;
            return first;
        }
        EdgeTag[] tags = edgeTags;
        if (tags == null) {
            tags = new EdgeTag[FLOW_KINDS];
            edgeTags = tags;
        }
        EdgeTag tag = tags[kind.ordinal()];
        if (tag == null) {
            tag = new EdgeTag(this, kind);
            tags[kind.ordinal()] = tag;
        }
        return tag;
    }

    /**
     * @return the number of bits held by the per-object memo sets of the
     * current memos.
     */
    static synchronized long memoBits() {
        long bits = 0;
        for (Memo m : memos.values()) {
            bits += m.pass.size();
        }
        return bits;
    }

    /**
     * @return an estimate of the bytes of the per-object memo sets of the
     * current memos (the sparse blocks, areas and tables they need).
     */
    private static synchronized long memoBytes() {
        long bytes = 0;
        for (Memo m : memos.values()) {
            bytes += sparseBytes(m.pass, m.types.indexer) + 16 + 8L * m.holes.length;
        }
        return bytes;
    }

    private static long sparseBytes(IndexerBitSet<CSObj> set, Indexer<CSObj> indexer) {
        int bitsPerBlock = SparseBitSet.WORDS_PER_BLOCK * Long.SIZE;
        int bitsPerArea = bitsPerBlock * SparseBitSet.BLOCKS_PER_AREA;
        long blocks = 0;
        long areas = 0;
        long lastBlock = -1;
        long lastArea = -1;
        long tableLength = 0;
        for (CSObj o : set) {
            int index = indexer.getIndex(o);
            if (index / bitsPerBlock != lastBlock) {
                lastBlock = index / bitsPerBlock;
                blocks++;
            }
            if (index / bitsPerArea != lastArea) {
                lastArea = index / bitsPerArea;
                areas++;
                tableLength = lastArea + 1;
            }
        }
        // object headers and array headers rounded to 16 bytes, references
        // of 4 bytes
        return 64 + 16 + 4 * tableLength + areas * (16 + 4L * SparseBitSet.BLOCKS_PER_AREA)
                + blocks * (16 + 8L * SparseBitSet.WORDS_PER_BLOCK);
    }

    private static void printStats() {
        System.err.println("[spd] TypeFilter stats: applications=" + STAT_APPLICATIONS.get()
                + " large=" + STAT_LARGE.get() + " tests=" + STAT_TESTS.get()
                + " filterMs=" + STAT_NANOS.get() / 1_000_000
                + " memos=" + memos.size() + " memoBits=" + memoBits()
                + " memoBytes=" + memoBytes());
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        applications++;
        Memo m = memo;
        if (m == null) {
            m = memoFor(type, indexer);
            memo = m;
        }
        PointsToSet result;
        if (STATS) {
            long start = System.nanoTime();
            long testsBefore = tests;
            result = filter(m, input);
            STAT_NANOS.addAndGet(System.nanoTime() - start);
            STAT_TESTS.addAndGet(tests - testsBefore);
            STAT_APPLICATIONS.incrementAndGet();
            if (input instanceof DelegatePointsToSet delegate
                    && delegate.set instanceof AbstractHybridSet<CSObj> hybrid
                    && hybrid.set instanceof GenericBitSet<CSObj>) {
                STAT_LARGE.incrementAndGet();
            }
        } else {
            result = filter(m, input);
        }
        if (VERIFY) {
            verify(input, result);
        }
        return result;
    }

    private PointsToSet filter(Memo m, PointsToSet input) {
        if (input instanceof DelegatePointsToSet delegate
                && delegate.set instanceof AbstractHybridSet<CSObj> hybrid
                && hybrid.set instanceof GenericBitSet<CSObj> in) {
            PointsToSet result = filterLarge(m, input, in, hybrid.getThreshold());
            if (result != null) {
                return result;
            }
        }
        PointsToSet result = ptsFactory.get();
        for (CSObj o : input) {
            if (passes(m, o)) {
                result.addObject(o);
            }
        }
        return result;
    }

    /**
     * @return the filtered set, or null if the copy of the input is not held
     * in a bit set (the caller then filters object by object). If every
     * object passes and the input is above the threshold, the result is the
     * input itself (as for {@link Identity}): consumers only read it.
     */
    private @Nullable PointsToSet filterLarge(Memo m, PointsToSet input,
                                              GenericBitSet<CSObj> in, int threshold) {
        // every index up to the input's highest one is checked, then one
        // pass over the words of the input checks its objects in the holes
        // and counts the passing ones
        extendMemo(m, in, in.indexLength());
        int passing = in.updateMemoAndCountByIndex(m.holes, m.pass, checker);
        if (passing > threshold) {
            if (passing == in.size()) {
                return input;
            }
            PointsToSet result = input.copy();
            if (!(result instanceof DelegatePointsToSet delegate
                    && delegate.set instanceof AbstractHybridSet<CSObj> hybrid
                    && hybrid.set instanceof GenericBitSet<CSObj> copied)) {
                return null;
            }
            copied.retainAll(m.pass);
            return result;
        }
        // a small result is collected from the words of input AND pass,
        // without copying the input
        PointsToSet small = ptsFactory.get();
        in.forEachIntersection(m.pass, small::addObject);
        return small;
    }

    /**
     * Moves the watermark of the memo up to the limit (exclusive), in
     * ascending order. An index is decided if the type memo already answers
     * for its object's type or if its object is in the input: the type
     * system is asked only for types of input objects, as checking each
     * input object would. The objects that pass are added to the memo.
     * Every other index (no object, or an object of a type not checked yet
     * that is not in the input) becomes a hole. The watermark moves past
     * each index once it is done, so a throwing check leaves that index and
     * the later ones unchecked.
     */
    private void extendMemo(Memo m, GenericBitSet<CSObj> input, int limit) {
        ObjectTypes types = m.types;
        for (int index = m.watermark; index < limit; ++index) {
            if (STATS) {
                tests++;
            }
            int typeId = types.idOfIndexOrMissing(index);
            int known = typeId < 0 ? -1 : m.typeResult(typeId);
            if (known < 0 && typeId >= 0 && input.containsIndex(index)) {
                known = checkByType(m, typeId) ? 1 : 0;
            }
            if (known < 0) {
                m.addHole(index);
            } else if (known == 1) {
                m.pass.addIndex(index);
            }
            m.watermark = index + 1;
        }
    }

    /**
     * Checks one object through the memo of its type id (the
     * object-by-object path keeps no per-object memo).
     */
    private boolean passes(Memo m, CSObj o) {
        if (STATS) {
            tests++;
        }
        return checkByType(m, m.types.idOf(o));
    }

    private boolean checkIndexWithMemo(int index) {
        Memo m = Objects.requireNonNull(memo);
        if (STATS) {
            tests++;
        }
        return checkByType(m, m.types.idOfIndex(index));
    }

    /**
     * Checks an object through the memo of its type id: objects of one type
     * share the answer, so each (guard type, object type) pair is checked
     * at most once.
     */
    private boolean checkByType(Memo m, int typeId) {
        int known = m.typeResult(typeId);
        if (known >= 0) {
            return known == 1;
        }
        // checked before the type is recorded: a throwing check leaves the
        // type unknown
        boolean ok = typeSystem.isAssignable(type, m.types.typeOf(typeId));
        m.recordType(typeId, ok);
        return ok;
    }

    private boolean check(CSObj o) {
        return typeSystem.isAssignable(type, o.getObject().getType());
    }

    private void verify(PointsToSet input, PointsToSet result) {
        PointsToSet expected = ptsFactory.get();
        input.objects()
                .filter(this::check)
                .forEach(expected::addObject);
        List<CSObj> want = new ArrayList<>(expected.getObjects());
        List<CSObj> got = new ArrayList<>(result.getObjects());
        boolean sameShape = expected.getClass() == result.getClass()
                && representation(expected) == representation(result);
        if (!want.equals(got) || !sameShape) {
            throw new AssertionError("TypeFilter differs for " + type + ": expected " + want
                    + " (" + representation(expected) + "), got " + got
                    + " (" + representation(result) + ")");
        }
        long n = VERIFIED.incrementAndGet();
        if (Long.bitCount(n) == 1) {
            System.err.println("[spd] TypeFilter verified applications: " + n);
        }
    }

    /**
     * @return 0 empty or singleton, 1 small set, 2 bit set, -1 another
     * points-to set implementation.
     */
    static int representation(PointsToSet pts) {
        if (!(pts instanceof DelegatePointsToSet delegate
                && delegate.set instanceof AbstractHybridSet<CSObj> hybrid)) {
            return -1;
        }
        return hybrid.set == null ? 0 : hybrid.set instanceof GenericBitSet<?> ? 2 : 1;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof TypeFilter that)) {
            return false;
        }
        return type.equals(that.type);
    }

    @Override
    public int hashCode() {
        return type.hashCode();
    }
}
