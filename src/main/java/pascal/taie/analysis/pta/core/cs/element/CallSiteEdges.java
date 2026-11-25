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
 * A plain edge (see {@link #isPlain}) is held as its callee alone and
 * rebuilt on read as an equal {@link Edge}, with the same hash code; every
 * other edge is held as the object that was added. Membership follows
 * {@link Edge#equals}: a plain edge never equals another edge, and two
 * plain edges are equal exactly when their callees are the same.
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
     * Each element is a {@link CSMethod} (the callee of a plain edge) or an
     * {@link Edge}.
     */
    private Object[] table = EMPTY;

    private Object single;

    private int size;

    private int modCount;

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

    @Override
    public boolean add(Edge<CSCallSite, CSMethod> edge) {
        Objects.requireNonNull(edge, "CallSiteEdges does not permit null");
        Object e = compact(edge);
        if (table == EMPTY) {
            if (size == 0) {
                single = e;
            } else if (matches(single, e)) {
                return false;
            } else {
                table = new Object[] {single, e};
                single = null;
            }
            ++size;
            ++modCount;
            return true;
        }
        int slot;
        if (isDense()) {
            if (containsDense(e)) {
                return false;
            }
            if (size < OpenHashSet.SMALL_LIMIT) {
                if (size == table.length) {
                    Object[] grown = new Object[Math.max(1,
                            Math.min(OpenHashSet.SMALL_LIMIT, size * 2))];
                    System.arraycopy(table, 0, grown, 0, size);
                    table = grown;
                }
                table[size++] = e;
                ++modCount;
                return true;
            }
            rehash(OpenHashSet.SMALL_LIMIT * 2);
            slot = findSlot(table, e);
        } else {
            slot = findSlot(table, e);
            if (table[slot] != null) {
                return false;
            }
            if ((size + 1) * 3L > table.length * 2L) {
                rehash(table.length * 2);
                slot = findSlot(table, e);
            }
        }
        table[slot] = e;
        ++size;
        ++modCount;
        return true;
    }

    @Override
    public boolean contains(Object o) {
        if (!(o instanceof Edge<?, ?> edge) || size == 0) {
            return false;
        }
        Object e = compact(edge);
        if (table == EMPTY) {
            return matches(single, e);
        }
        if (isDense()) {
            return containsDense(e);
        }
        return table[findSlot(table, e)] != null;
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
        if (table == EMPTY) {
            return matches(single, callee);
        }
        if (isDense()) {
            return containsDense(callee);
        }
        return table[findSlot(table, callee)] != null;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public Iterator<Edge<CSCallSite, CSMethod>> iterator() {
        return new Iterator<>() {

            private final int expectedModCount = modCount;

            private final Object[] tab = table;

            private Object pendingSingle = tab == EMPTY ? single : null;

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
                if (modCount != expectedModCount) {
                    throw new ConcurrentModificationException();
                }
                if (pendingSingle != null) {
                    Object e = pendingSingle;
                    pendingSingle = null;
                    return expand(e);
                }
                if (index >= tab.length) {
                    throw new NoSuchElementException();
                }
                Object e = tab[index];
                index = advance(index + 1);
                return expand(e);
            }
        };
    }

    /**
     * @return the element that holds {@code edge}: its callee if it is
     * plain, otherwise the edge itself.
     */
    private Object compact(Edge<?, ?> edge) {
        return isPlain(edge) ? edge.getCallee() : edge;
    }

    @SuppressWarnings("unchecked")
    private Edge<CSCallSite, CSMethod> expand(Object e) {
        return e instanceof CSMethod callee
                ? plainEdge(callee)
                : (Edge<CSCallSite, CSMethod>) e;
    }

    /**
     * @return the hash code of the edge that {@code e} holds.
     */
    private int hash(Object e) {
        return e instanceof CSMethod callee
                ? Hashes.hash(plainKind, site, callee)
                : e.hashCode();
    }

    /**
     * @return whether the edge held by {@code stored} equals the one held by
     * {@code e}, as {@code stored.equals(e)} of the edges themselves.
     */
    private static boolean matches(Object stored, Object e) {
        if (e instanceof CSMethod) {
            return stored == e;
        }
        return !(stored instanceof CSMethod) && stored.equals(e);
    }

    private boolean isDense() {
        return table.length <= OpenHashSet.SMALL_LIMIT;
    }

    private boolean containsDense(Object e) {
        for (int i = 0; i < size; ++i) {
            if (matches(table[i], e)) {
                return true;
            }
        }
        return false;
    }

    private void rehash(int capacity) {
        Object[] old = table;
        Object[] fresh = new Object[capacity];
        for (Object e : old) {
            if (e != null) {
                fresh[findSlot(fresh, e)] = e;
            }
        }
        table = fresh;
    }

    private int findSlot(Object[] tab, Object e) {
        int h = hash(e);
        int mask = tab.length - 1;
        int i = (h ^ (h >>> 16)) & mask;
        Object cur;
        while ((cur = tab[i]) != null && !matches(cur, e)) {
            i = (i + 1) & mask;
        }
        return i;
    }
}
