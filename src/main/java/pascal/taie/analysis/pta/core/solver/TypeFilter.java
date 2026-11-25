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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
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
 * most once per (guard type, object type); the type id of an object is
 * read from a flat array over the solver's object index, shared by all
 * guard types (the object itself is read only the first time its type id
 * is assigned). An input held in a bit set is filtered word by word
 * through a second memo per guard type, a bit set over the object index
 * that is complete below a watermark: every object below it is decided,
 * and the set marks either the passing or the failing ones (whichever are
 * fewer, so a guard that almost every object passes marks few). The
 * watermark is raised to the highest object of each such input, deciding
 * every object up to it, including objects that were never in an input of
 * the guard (this asks the type system for their types too, which gives
 * the same answers as long as the type system's assignability test has
 * no side effect on its answers). An index that held no object when the
 * watermark passed it (a reserved index range of the object indexer) is
 * kept as a hole and decided when it first occurs in an input. The bits
 * of input AND marks are counted, and the result is the input AND the
 * passing objects (the input itself if all pass). A smaller input is
 * filtered object by object through the type memo alone. The memos of the
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
         * @return the type id of the object of the index, or -1 if the index
         * holds no object (yet); the object is read from the indexer only if
         * its id is not assigned yet.
         */
        int idOfIndexOrEmpty(int index) {
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
     * Memo of one guard type: per object type id (see {@link ObjectTypes})
     * the types already checked, and those that passed; and the objects
     * decided below a watermark, as the marks of one polarity (see the
     * class comment).
     */
    private static final class Memo {

        final ObjectTypes types;

        private final Indexer<CSObj> indexer;

        private long[] typeKnown = new long[0];

        private long[] typePass = new long[0];

        /**
         * Every index below it is decided, except the holes.
         */
        int watermark;

        /**
         * True if the marks are the passing objects below the watermark,
         * false if they are the failing ones.
         */
        boolean marksPass = true;

        /**
         * The marked objects below the watermark; null while there are
         * none.
         */
        @Nullable IndexerBitSet<CSObj> marks;

        /**
         * The number of marked objects, and of decided objects (the indexes
         * below the watermark that are not holes).
         */
        int marked;

        int decided;

        /**
         * The indexes below the watermark that held no object when it
         * passed them, and were not in an input since; null while there are
         * none.
         */
        @Nullable IndexerBitSet<CSObj> holes;

        Memo(Indexer<CSObj> indexer, ObjectTypes types) {
            this.indexer = indexer;
            this.types = types;
        }

        /**
         * Records the answer of a decided object.
         */
        void decide(int index, boolean passes) {
            if (passes == marksPass) {
                IndexerBitSet<CSObj> set = marks;
                if (set == null) {
                    set = new IndexerBitSet<>(indexer, true);
                    marks = set;
                }
                set.addIndex(index);
                ++marked;
            }
            ++decided;
        }

        void addHole(int index) {
            IndexerBitSet<CSObj> set = holes;
            if (set == null) {
                set = new IndexerBitSet<>(indexer, true);
                holes = set;
            }
            set.addIndex(index);
        }

        /**
         * Switches the polarity if more than two thirds of the decided
         * objects are marked; afterwards fewer than a third are. The decided
         * objects must more than double between two switches, so all
         * switches together cost time linear in the highest watermark.
         */
        void balance() {
            IndexerBitSet<CSObj> old = marks;
            if (old == null || 3L * marked <= 2L * decided) {
                return;
            }
            IndexerBitSet<CSObj> gaps = holes;
            IndexerBitSet<CSObj> flipped = new IndexerBitSet<>(indexer, true);
            int count = 0;
            for (int i = 0; i < watermark; ++i) {
                if (!old.containsIndex(i) && (gaps == null || !gaps.containsIndex(i))) {
                    flipped.addIndex(i);
                    ++count;
                }
            }
            marks = count == 0 ? null : flipped;
            marked = count;
            marksPass = !marksPass;
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

    private @Nullable Memo memo;

    private long applications;

    /**
     * Whether the measurement counters below are kept; set by the solver
     * for each solve (see {@link #setStats}). They change no result and no
     * order.
     */
    private static boolean stats;

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
     * Turns the measurement counters of all type filters on or off.
     */
    static void setStats(boolean on) {
        stats = on;
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
     * memos decided, the objects and holes they hold, and the memos that
     * mark the failing objects, each shared memo counted once.
     *
     * @return the summary line, or the empty text if the counters are off.
     */
    static String statsLine(Collection<TypeFilter> filters) {
        if (!stats) {
            return "";
        }
        long apps = 0;
        long large = 0;
        long bits = 0;
        long tests = 0;
        long memoDecided = 0;
        long memoMarked = 0;
        long memoHoles = 0;
        long failMarking = 0;
        Set<Memo> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (TypeFilter f : filters) {
            apps += f.applications;
            large += f.largeApplications;
            bits += f.inputBits;
            tests += f.typeTests;
            Memo m = f.memo;
            if (m != null && seen.add(m)) {
                memoDecided += m.decided;
                memoMarked += m.marked;
                IndexerBitSet<CSObj> holes = m.holes;
                memoHoles += holes == null ? 0 : holes.size();
                failMarking += m.marksPass ? 0 : 1;
            }
        }
        return "filters=" + filters.size()
                + " applications=" + apps
                + " large_applications=" + large
                + " input_bits=" + bits
                + " type_tests=" + tests
                + " memo_decided_objects=" + memoDecided
                + " memo_marked_objects=" + memoMarked
                + " memo_holes=" + memoHoles
                + " memo_fail_marking=" + failMarking;
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
            PointsToSet result = filterLarge(m, delegate, in, hybrid.getThreshold());
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
    private @Nullable PointsToSet filterLarge(Memo m, DelegatePointsToSet input,
                                              GenericBitSet<CSObj> in, int threshold) {
        if (stats) {
            ++largeApplications;
        }
        // every object of the input is decided, then the marked ones are
        // counted word by word
        raiseWatermark(m, in.indexLength());
        decideFilledHoles(m, in);
        IndexerBitSet<CSObj> marks = m.marks;
        int size = in.size();
        int marked = marks == null ? 0 : in.countIntersection(marks);
        int passing = m.marksPass ? marked : size - marked;
        if (passing > threshold) {
            if (passing == size) {
                return input;
            }
            // some objects pass and some fail, so there are marks
            IndexerBitSet<CSObj> mk = Objects.requireNonNull(marks);
            if (m.marksPass && input.canIntersectLarge(mk)) {
                // built from the words of input AND pass, without copying
                // the input
                return input.largeIntersection(mk);
            }
            PointsToSet result = input.copy();
            if (!(result instanceof DelegatePointsToSet delegate
                    && delegate.set instanceof AbstractHybridSet<CSObj> hybrid
                    && hybrid.set instanceof GenericBitSet<CSObj> copied)) {
                return null;
            }
            if (m.marksPass) {
                copied.retainAll(mk);
            } else {
                copied.removeAll(mk);
            }
            return result;
        }
        // a small result is collected in the order of the input, without
        // copying it
        PointsToSet small = ptsFactory.get();
        if (passing == 0) {
            return small;
        }
        if (m.marksPass) {
            in.forEachIntersection(Objects.requireNonNull(marks), small::addObject);
        } else {
            for (CSObj o : in) {
                if (marks == null || !marks.contains(o)) {
                    small.addObject(o);
                }
            }
        }
        return small;
    }

    /**
     * Decides every index from the watermark up to the given length (an
     * index without an object becomes a hole) and raises the watermark to
     * it. The watermark passes an index only after it was decided: a
     * throwing check leaves that index and the later ones undecided.
     */
    private void raiseWatermark(Memo m, int length) {
        if (length <= m.watermark) {
            return;
        }
        ObjectTypes types = m.types;
        for (int i = m.watermark; i < length; ++i) {
            int typeId = types.idOfIndexOrEmpty(i);
            if (typeId < 0) {
                m.addHole(i);
            } else {
                m.decide(i, checkByType(m, typeId));
            }
            m.watermark = i + 1;
        }
        m.balance();
    }

    /**
     * Decides the holes of the memo that hold an object of the input now
     * (the objects of an input exist).
     */
    private void decideFilledHoles(Memo m, GenericBitSet<CSObj> in) {
        IndexerBitSet<CSObj> holes = m.holes;
        // counted by the blocks of the holes (intersects would unpack a
        // packed input)
        if (holes == null || holes.countIntersection(in) == 0) {
            return;
        }
        List<CSObj> filled = new ArrayList<>();
        in.forEachIntersection(holes, filled::add);
        for (CSObj o : filled) {
            // decided before the hole is removed: a throwing check leaves
            // the hole
            m.decide(indexer.getIndex(o), checkByType(m, m.types.idOf(o)));
            holes.remove(o);
        }
        if (holes.isEmpty()) {
            m.holes = null;
        }
    }

    private boolean passes(Memo m, CSObj o) {
        return checkByType(m, m.types.idOf(o));
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
