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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;
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
 * (guard type, object) pair is checked at most once per solver. An input
 * held in a bit set is filtered by bit operations: its unchecked objects
 * are checked once, then the result is the input AND pass. A smaller input
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
     * Memo of one guard type: objects already checked, and those that passed.
     */
    private static final class Memo {

        final IndexerBitSet<CSObj> known;

        final IndexerBitSet<CSObj> pass;

        Memo(Indexer<CSObj> indexer) {
            known = new IndexerBitSet<>(indexer, true);
            pass = new IndexerBitSet<>(indexer, true);
        }
    }

    private static @Nullable Indexer<CSObj> memoIndexer;

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
     * The delta that a solver is propagating and the result of this filter
     * on it, or null outside a propagation that applied it; set and cleared
     * by {@link DeltaTransfers}.
     */
    @Nullable PointsToSet deltaInput;

    @Nullable PointsToSet deltaResult;

    public TypeFilter(Type type, Solver solver) {
        this.type = type;
        this.typeSystem = solver.getTypeSystem();
        this.ptsFactory = solver::makePointsToSet;
        this.indexer = solver.getCSManager().getObjectIndexer();
    }

    private static synchronized Memo memoFor(Type type, Indexer<CSObj> indexer) {
        if (memoIndexer != indexer) {
            memoIndexer = indexer;
            memos = new HashMap<>();
        }
        return memos.computeIfAbsent(type, t -> new Memo(indexer));
    }

    /**
     * Drops the memos (and with them the last solver's objects) when the
     * world is reset, or when a solver releases its state after its fixed
     * point (the memos only cache {@link #passes}; a later application
     * builds them again).
     */
    static synchronized void clearMemos() {
        memoIndexer = null;
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

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        applications++;
        Memo m = memo;
        if (m == null) {
            m = memoFor(type, indexer);
            memo = m;
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
        // read-only subset tests first: after warm-up most inputs are fully
        // known, and many pass entirely
        if (!m.known.containsAll(in)) {
            for (CSObj o : m.known.addAllDiff(in)) {
                if (check(o)) {
                    m.pass.add(o);
                }
            }
        }
        GenericBitSet<CSObj> out = in;
        PointsToSet result = input;
        if (!m.pass.containsAll(in)) {
            result = input.copy();
            if (!(result instanceof DelegatePointsToSet delegate
                    && delegate.set instanceof AbstractHybridSet<CSObj> hybrid
                    && hybrid.set instanceof GenericBitSet<CSObj> copied)) {
                return null;
            }
            copied.retainAll(m.pass);
            out = copied;
        }
        if (out.size() > threshold) {
            return result;
        }
        PointsToSet small = ptsFactory.get();
        for (CSObj o : out) {
            small.addObject(o);
        }
        return small;
    }

    private boolean passes(Memo m, CSObj o) {
        if (m.known.contains(o)) {
            return m.pass.contains(o);
        }
        m.known.add(o);
        boolean ok = check(o);
        if (ok) {
            m.pass.add(o);
        }
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
