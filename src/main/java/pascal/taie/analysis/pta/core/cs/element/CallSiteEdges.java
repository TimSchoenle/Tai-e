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

package pascal.taie.analysis.pta.core.cs.element;

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.util.Hashes;
import pascal.taie.util.collection.OpenHashSet;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;

/**
 * Add-only set of the call edges out of one call site, laid out exactly as
 * an {@link OpenHashSet} of the same edges: up to
 * {@link OpenHashSet#SMALL_LIMIT} edges a dense insertion-ordered array,
 * then an open-addressing table with linear probing on the edges' hash
 * codes. So the slots, and the iteration order, equal those of an
 * {@link OpenHashSet} that receives the same {@link #add} calls.
 * <p>
 * A plain edge (see {@link #isPlain}) is held as its callee alone, a
 * sourced edge (see {@link #sourceOf}) as its callee and, at the same index
 * of a parallel array, its {@link EdgeSource}; both are rebuilt on read as
 * an equal edge of the same class, with the same hash code. Every other
 * edge is held as the object that was added. Membership follows
 * {@link Edge#equals}: a plain edge never equals another edge, two plain
 * edges are equal exactly when their callees are the same, and two sourced
 * edges exactly when their callees are the same and their sources equal.
 */
final class CallSiteEdges extends AbstractSet<Edge<CSCallSite, CSMethod>> {

    private static final Object[] EMPTY = {};

    private final CSCallSite site;

    /**
     * Kind of the plain edges of {@link #site}; null if its invoke has no
     * known kind, then no edge is plain.
     */
    private final @Nullable CallKind plainKind;

    /**
     * Each element is a {@link CSMethod} (the callee of a plain edge, or of
     * a sourced edge if {@link #sources} holds a source at its index) or an
     * {@link Edge}.
     */
    private Object[] table = EMPTY;

    /**
     * The sources of the sourced edges. While {@link #table} is empty: the
     * {@link EdgeSource} of {@link #single}, or null if it is not a sourced
     * edge. Otherwise an {@code EdgeSource[]} as long as {@link #table},
     * with the sources at the indices of their callees, or null while no
     * sourced edge is in {@link #table}. One field for both, so that the set
     * takes no more space than without sourced edges.
     */
    private @Nullable Object sources;

    /**
     * The only element while {@link #table} is empty and one edge is held.
     */
    private Object single;

    /**
     * Number of edges held; as the set is add-only, it also counts the
     * modifications, for the iterators' fail-fast check.
     */
    private int size;

    CallSiteEdges(CSCallSite site, @Nullable CallKind plainKind) {
        this.site = site;
        this.plainKind = plainKind;
    }

    /**
     * @return whether {@code edge} is a plain edge of this call site: of
     * class {@link Edge} itself, of the call site's own kind, from this call
     * site to a {@link CSMethod}. Such an edge equals
     * {@link #plainEdge plainEdge(edge.getCallee())}.
     */
    boolean isPlain(Edge<?, ?> edge) {
        return plainKind != null
                && edge.getClass() == Edge.class
                && edge.getKind() == plainKind
                && edge.getCallSite() == site
                && edge.getCallee() instanceof CSMethod;
    }

    /**
     * @return a new plain edge from this call site to {@code callee}.
     */
    Edge<CSCallSite, CSMethod> plainEdge(CSMethod callee) {
        return new Edge<>(plainKind, site, callee);
    }

    /**
     * @return the source of {@code edge} if it is a sourced edge of this
     * call site: a {@link SourcedEdge} with a source, from this call site to
     * a {@link CSMethod}; otherwise null. Such an edge equals
     * {@code sourceOf(edge).edge(site, edge.getCallee())}.
     */
    @Nullable
    EdgeSource sourceOf(Edge<?, ?> edge) {
        return edge instanceof SourcedEdge sourced
                && edge.getCallSite() == site
                && edge.getCallee() instanceof CSMethod
                ? sourced.getSource()
                : null;
    }

    @Override
    public boolean add(Edge<CSCallSite, CSMethod> edge) {
        Objects.requireNonNull(edge, "CallSiteEdges does not permit null");
        EdgeSource source = sourceOf(edge);
        Object e = source != null ? edge.getCallee() : compact(edge);
        if (table == EMPTY) {
            return addToSingle(e, source);
        }
        int slot;
        if (isDense()) {
            if (containsDense(e, source)) {
                return false;
            }
            if (size < OpenHashSet.SMALL_LIMIT) {
                if (size == table.length) {
                    int capacity = Math.max(1,
                            Math.min(OpenHashSet.SMALL_LIMIT, size * 2));
                    table = Arrays.copyOf(table, capacity);
                    EdgeSource[] srcs = tableSources();
                    if (srcs != null) {
                        sources = Arrays.copyOf(srcs, capacity);
                    }
                }
                slot = size;
            } else {
                rehash(OpenHashSet.SMALL_LIMIT * 2);
                slot = findSlot(table, tableSources(), e, source);
            }
        } else {
            slot = findSlot(table, tableSources(), e, source);
            if (table[slot] != null) {
                return false;
            }
            if ((size + 1) * 3L > table.length * 2L) {
                rehash(table.length * 2);
                slot = findSlot(table, tableSources(), e, source);
            }
        }
        table[slot] = e;
        if (source != null) {
            EdgeSource[] srcs = tableSources();
            if (srcs == null) {
                srcs = new EdgeSource[table.length];
                sources = srcs;
            }
            srcs[slot] = source;
        }
        ++size;
        return true;
    }

    /**
     * {@link #add} while {@link #table} is empty, so at most one edge is
     * held, in {@link #single} with its source in {@link #sources}.
     */
    private boolean addToSingle(Object e, @Nullable EdgeSource source) {
        if (size == 0) {
            single = e;
            sources = source;
            size = 1;
            return true;
        }
        EdgeSource singleSource = (EdgeSource) sources;
        if (matches(single, singleSource, e, source)) {
            return false;
        }
        table = new Object[] {single, e};
        single = null;
        sources = singleSource == null && source == null
                ? null
                : new EdgeSource[] {singleSource, source};
        size = 2;
        return true;
    }

    @Override
    public boolean contains(Object o) {
        if (!(o instanceof Edge<?, ?> edge) || size == 0) {
            return false;
        }
        EdgeSource source = sourceOf(edge);
        Object e = source != null ? edge.getCallee() : compact(edge);
        if (table == EMPTY) {
            return matches(single, (EdgeSource) sources, e, source);
        }
        if (isDense()) {
            return containsDense(e, source);
        }
        return table[findSlot(table, tableSources(), e, source)] != null;
    }

    /**
     * @return whether this set holds the plain edge of {@code kind} to
     * {@code callee}, found without an edge object; false if {@code kind}
     * is not the kind of the plain edges of this call site
     */
    boolean containsPlain(CallKind kind, CSMethod callee) {
        if (kind != plainKind || size == 0) {
            return false;
        }
        // a plain edge is stored as its callee, without an edge source
        if (table == EMPTY) {
            return matches(single, (EdgeSource) sources, callee, null);
        }
        if (isDense()) {
            return containsDense(callee, null);
        }
        return table[findSlot(table, tableSources(), callee, null)] != null;
    }

    /**
     * @return whether this set holds the sourced edge
     * {@code source.edge(site, callee)}, found without an edge object: the
     * same answer as {@link #contains} of that edge
     * @throws NullPointerException if {@code source} is null: a null source
     * would ask for a plain edge ({@link #containsPlain})
     */
    boolean containsSourced(EdgeSource source, CSMethod callee) {
        Objects.requireNonNull(source, "source");
        if (size == 0) {
            return false;
        }
        // a sourced edge is stored as its callee with its source
        if (table == EMPTY) {
            return matches(single, (EdgeSource) sources, callee, source);
        }
        if (isDense()) {
            return containsDense(callee, source);
        }
        return table[findSlot(table, tableSources(), callee, source)] != null;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public Iterator<Edge<CSCallSite, CSMethod>> iterator() {
        return new Iterator<>() {

            private final int expectedSize = size;

            private final Object[] tab = table;

            private final EdgeSource @Nullable [] srcs = tableSources();

            private Object pendingSingle = tab == EMPTY ? single : null;

            private final @Nullable EdgeSource singleSource =
                    tab == EMPTY ? (EdgeSource) sources : null;

            private int index = advance(0);

            private int advance(int from) {
                int i = from;
                while (i < tab.length && tab[i] == null) {
                    ++i;
                }
                return i;
            }

            @Override
            public boolean hasNext() {
                return pendingSingle != null || index < tab.length;
            }

            @Override
            public Edge<CSCallSite, CSMethod> next() {
                if (size != expectedSize) {
                    throw new ConcurrentModificationException();
                }
                if (pendingSingle != null) {
                    Object e = pendingSingle;
                    pendingSingle = null;
                    return expand(e, singleSource);
                }
                if (index >= tab.length) {
                    throw new NoSuchElementException();
                }
                int i = index;
                index = advance(i + 1);
                return expand(tab[i], srcs == null ? null : srcs[i]);
            }
        };
    }

    /**
     * @return the parallel array of the sources of the edges in
     * {@link #table}, or null if none of them is a sourced edge or the
     * table is empty.
     */
    private EdgeSource @Nullable [] tableSources() {
        return table == EMPTY ? null : (EdgeSource[]) sources;
    }

    /**
     * @return the element that holds {@code edge}, not a sourced one: its
     * callee if it is plain, otherwise the edge itself.
     */
    private Object compact(Edge<?, ?> edge) {
        return isPlain(edge) ? edge.getCallee() : edge;
    }

    /**
     * @return the edge that the element {@code e} with the source
     * {@code source} (null if none) holds.
     */
    @SuppressWarnings("unchecked")
    private Edge<CSCallSite, CSMethod> expand(Object e, @Nullable EdgeSource source) {
        if (source != null) {
            return source.edge(site, (CSMethod) e);
        }
        return e instanceof CSMethod callee
                ? plainEdge(callee)
                : (Edge<CSCallSite, CSMethod>) e;
    }

    /**
     * @return the hash code of the edge that the element {@code e} with the
     * source {@code source} (null if none) holds.
     */
    private int hash(Object e, @Nullable EdgeSource source) {
        if (source != null) {
            return source.edgeHashCode(site, (CSMethod) e);
        }
        return e instanceof CSMethod callee
                ? Hashes.hash(plainKind, site, callee)
                : e.hashCode();
    }

    /**
     * @return whether the edge held by {@code stored} with the source
     * {@code storedSource} equals the one held by {@code e} with the source
     * {@code source}, as {@code stored.equals(e)} of the edges themselves.
     */
    private static boolean matches(Object stored, @Nullable EdgeSource storedSource,
                                   Object e, @Nullable EdgeSource source) {
        if (source != null) {
            return storedSource != null && stored == e
                    && (storedSource == source || storedSource.equals(source));
        }
        if (storedSource != null) {
            return false;
        }
        if (e instanceof CSMethod) {
            return stored == e;
        }
        return !(stored instanceof CSMethod) && stored.equals(e);
    }

    private boolean isDense() {
        return table.length <= OpenHashSet.SMALL_LIMIT;
    }

    private boolean containsDense(Object e, @Nullable EdgeSource source) {
        EdgeSource[] srcs = tableSources();
        for (int i = 0; i < size; ++i) {
            if (matches(table[i], srcs == null ? null : srcs[i], e, source)) {
                return true;
            }
        }
        return false;
    }

    private void rehash(int capacity) {
        Object[] old = table;
        EdgeSource[] oldSources = tableSources();
        Object[] fresh = new Object[capacity];
        EdgeSource[] freshSources = oldSources == null ? null : new EdgeSource[capacity];
        for (int i = 0; i < old.length; ++i) {
            Object e = old[i];
            if (e != null) {
                EdgeSource source = oldSources == null ? null : oldSources[i];
                int slot = findSlot(fresh, freshSources, e, source);
                fresh[slot] = e;
                if (freshSources != null) {
                    freshSources[slot] = source;
                }
            }
        }
        table = fresh;
        sources = freshSources;
    }

    private int findSlot(Object[] tab, EdgeSource @Nullable [] srcs,
                         Object e, @Nullable EdgeSource source) {
        int h = hash(e, source);
        int mask = tab.length - 1;
        int i = (h ^ (h >>> 16)) & mask;
        Object cur;
        while ((cur = tab[i]) != null
                && !matches(cur, srcs == null ? null : srcs[i], e, source)) {
            i = (i + 1) & mask;
        }
        return i;
    }
}
