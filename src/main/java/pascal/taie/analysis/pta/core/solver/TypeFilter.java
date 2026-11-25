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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
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
 * iteration order as inserting them one by one. Per guard type, a memo
 * remembers which objects were already checked (known) and which passed
 * (pass), both bit sets over the solver's object index, so each
 * (guard type, object) pair is tested at most once per solver. The test of
 * an object goes through a second memo per guard type over dense ids of
 * the objects' types (objects of one type share the answer), so the type
 * system is asked at most once per (guard type, object type). An input
 * held in a bit set is filtered word by word: in one pass over its words
 * only the bits of input AND NOT known are checked (and added to the memo)
 * by their object index, whose type id is read from a flat array (the
 * object itself is read only the first time its type id is assigned),
 * and the bits of input AND pass are counted; the result is the input AND
 * pass (the input itself if all pass). A smaller input
 * is filtered object by object through the same memo. The memos of the
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

    static {
        World.registerResetCallback(TypeFilter::clearMemos);
        if (VERIFY) {
            Runtime.getRuntime().addShutdownHook(new Thread(() ->
                    System.err.println("[spd] TypeFilter verified applications: " + VERIFIED.get())));
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

        Type typeOf(int id) {
            return types.get(id);
        }

        /**
         * @return the estimated bytes of the type id table: a 16-byte array
         * header and four bytes an object index.
         */
        long bytes() {
            return 16L + 4L * idPlusOne.length;
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
     * Memo of one guard type: objects already checked, and those that
     * passed; and per object type id (see {@link ObjectTypes}) the types
     * already checked, and those that passed.
     */
    private static final class Memo {

        final IndexerBitSet<CSObj> known;

        final IndexerBitSet<CSObj> pass;

        final ObjectTypes types;

        private long[] typeKnown = new long[0];

        private long[] typePass = new long[0];

        Memo(Indexer<CSObj> indexer, ObjectTypes types) {
            known = new IndexerBitSet<>(indexer, true);
            pass = new IndexerBitSet<>(indexer, true);
            this.types = types;
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

        /**
         * @return the estimated bytes of this memo's bits: the known and pass
         * sets in packed form and the two type word arrays (a 16-byte array
         * header and eight bytes a word each).
         */
        long bytes() {
            return known.packedBytes() + pass.packedBytes()
                    + 32L + 8L * (typeKnown.length + typePass.length);
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
     * Whether the measurement counters below are kept; turned on by the
     * solver that created this filter (see {@link #enableStats}). They
     * change no result and no order.
     */
    private boolean stats;

    /**
     * Applications that took the bit set path, objects in the inputs of
     * all applications, and the assignability tests made for an object
     * type the memo did not know yet.
     */
    private long largeApplications;

    private long inputBits;

    private long typeTests;

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
     * Turns the measurement counters of this filter on.
     */
    void enableStats() {
        stats = true;
    }

    long largeApplications() {
        return largeApplications;
    }

    long inputBits() {
        return inputBits;
    }

    long typeTests() {
        return typeTests;
    }

    /**
     * Sums the measurement counters of the filters, with the objects their
     * memos know and those that pass, and the estimated bytes of the memos
     * (their known and pass bit sets in the packed form of
     * {@link GenericBitSet#packedBytes()}, their type words, and the shared
     * table of object type ids), each shared memo and table counted once.
     *
     * @param counting whether the solver that created the filters keeps
     *                 the counters
     * @return the summary line, or the empty text if the counters are off.
     */
    static String statsLine(Collection<TypeFilter> filters, boolean counting) {
        if (!counting) {
            return "";
        }
        long apps = 0;
        long large = 0;
        long bits = 0;
        long tests = 0;
        long memoKnown = 0;
        long memoPass = 0;
        long memoBytes = 0;
        Set<Memo> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Set<ObjectTypes> seenTypes = Collections.newSetFromMap(new IdentityHashMap<>());
        for (TypeFilter f : filters) {
            apps += f.applications;
            large += f.largeApplications;
            bits += f.inputBits;
            tests += f.typeTests;
            Memo m = f.memo;
            if (m != null && seen.add(m)) {
                memoKnown += m.known.size();
                memoPass += m.pass.size();
                memoBytes += m.bytes();
                if (seenTypes.add(m.types)) {
                    memoBytes += m.types.bytes();
                }
            }
        }
        return "filters=" + filters.size()
                + " applications=" + apps
                + " large_applications=" + large
                + " input_bits=" + bits
                + " type_tests=" + tests
                + " memo_known_objects=" + memoKnown
                + " memo_pass_objects=" + memoPass
                + " memo_bytes=" + memoBytes;
    }

    /**
     * The block of the guards: per memo (one guard type) that the filters
     * hold, the filters sharing it with their applications, large
     * applications and input bits, and the objects the memo knows, passes
     * and fails at this point (the solver logs it at the exit of the
     * solve). Lists the {@code limit} guards with the most failing objects
     * (ties by the most known objects, then by the guard type's name),
     * after a line with the number of guards, of guards that pass every
     * known object and of guards that fail every known object.
     *
     * @return the block, or the empty text if the counters are off.
     */
    static String guardsBlock(Collection<TypeFilter> filters, boolean counting, int limit) {
        if (!counting) {
            return "";
        }
        Map<Memo, GuardRow> rows = new IdentityHashMap<>();
        for (TypeFilter f : filters) {
            Memo m = f.memo;
            if (m != null) {
                rows.computeIfAbsent(m, k -> new GuardRow(f.type.getName(),
                        k.known.size(), k.pass.size())).add(f);
            }
        }
        List<GuardRow> sorted = new ArrayList<>(rows.values());
        sorted.sort(Comparator.comparingLong((GuardRow r) -> r.known - r.pass).reversed()
                .thenComparing(Comparator.comparingLong((GuardRow r) -> r.known).reversed())
                .thenComparing(r -> r.type));
        long allPass = sorted.stream().filter(r -> r.known > 0 && r.pass == r.known).count();
        long allFail = sorted.stream().filter(r -> r.pass == 0 && r.known > 0).count();
        StringBuilder block = new StringBuilder("guards=").append(sorted.size())
                .append(" all_pass=").append(allPass).append(" all_fail=").append(allFail);
        for (GuardRow r : sorted.subList(0, Math.min(limit, sorted.size()))) {
            block.append('\n').append(r);
        }
        return block.toString();
    }

    /**
     * One guard of {@link #guardsBlock}.
     */
    private static final class GuardRow {

        private final String type;

        private final long known;

        private final long pass;

        private long filters;

        private long applications;

        private long largeApplications;

        private long inputBits;

        private GuardRow(String type, long known, long pass) {
            this.type = type;
            this.known = known;
            this.pass = pass;
        }

        private void add(TypeFilter f) {
            ++filters;
            applications += f.applications;
            largeApplications += f.largeApplications;
            inputBits += f.inputBits;
        }

        @Override
        public String toString() {
            return "guard " + type + " filters=" + filters + " applications=" + applications
                    + " large_applications=" + largeApplications + " input_bits=" + inputBits
                    + " known=" + known + " pass=" + pass + " fail=" + (known - pass);
        }
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

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        applications++;
        Memo m = memo;
        if (m == null) {
            m = memoFor(type, indexer);
            memo = m;
        }
        if (stats) {
            inputBits += input.size();
        }
        PointsToSet result = filter(m, input);
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
        if (stats) {
            ++largeApplications;
        }
        // one pass over the words of the input: only its unchecked objects
        // are checked (and added to the memo), the passing ones are counted
        int passing = in.updateMemoAndCountByIndex(m.known, m.pass, checker);
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

    private boolean passes(Memo m, CSObj o) {
        if (m.known.contains(o)) {
            return m.pass.contains(o);
        }
        // checked before it is marked known: a throwing check leaves the
        // object unknown
        boolean ok = checkByType(m, m.types.idOf(o));
        m.known.add(o);
        if (ok) {
            m.pass.add(o);
        }
        return ok;
    }

    private boolean checkIndexWithMemo(int index) {
        Memo m = Objects.requireNonNull(memo);
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
        if (stats) {
            ++typeTests;
        }
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
