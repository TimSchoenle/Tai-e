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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.plugin.exception.CSMethodThrowResult;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AbstractResultHolder;
import pascal.taie.util.ResultHolder;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.RandomAccess;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * Represents context-sensitive methods.
 */
public class CSMethod extends AbstractCSElement {

    /**
     * Below this index, the first sourced edge starts a dense store, as it
     * takes no more bytes than a sparse one there: a dense store up to
     * index 13 takes at most 16 + 14 * 4 = 72 bytes, a sparse store with one
     * source 72 bytes too (the object 24, a one-element {@code int[]} and
     * {@code EdgeSource[]} 24 each; see {@link SparseSources#bytes}).
     */
    private static final int SPARSE_MIN_INDEX = 14;

    private final JMethod method;

    /**
     * Call edges to this CS method, in the order they were added: a plain
     * edge (see {@link CSCallSite#isPlainEdge}) as its {@link CSCallSite},
     * a sourced edge (see {@link CSCallSite#sourceOf}) as its
     * {@link CSCallSite} with its source at the same index of
     * {@link #sources}, any other edge as the {@link Edge} object.
     */
    private final ArrayList<Object> edges = new ArrayList<>(4);

    /**
     * The sources of the sourced edges by their indices in {@link #edges};
     * null while no sourced edge was added. Either an {@code EdgeSource[]}
     * with the sources at their indices, null at the other indices, which
     * may be shorter than {@link #edges} (dense), or a
     * {@link SparseSources} with the sourced indices only. A sourced edge
     * keeps the form that takes fewer bytes: the sparse one while fewer
     * than half of the indices up to the last sourced one are sourced, and
     * once dense, the store stays dense.
     */
    private @Nullable Object sources;

    private final ResultHolder resultHolder = new AbstractResultHolder() {};

    /**
     * The exception analysis's result on this CS method; null until that
     * analysis first propagates an exception here.
     */
    private CSMethodThrowResult throwResult;

    CSMethod(JMethod method, Context context) {
        super(context);
        this.method = method;
    }

    /**
     * @return the method (without context).
     */
    public JMethod getMethod() {
        return method;
    }

    public void addEdge(Edge<CSCallSite, CSMethod> edge) {
        // The caller has ensured that each edge added to CSMethod is unique
        CSCallSite callSite = edge.getCallSite();
        EdgeSource source = edge.getCallee() == this ? callSite.sourceOf(edge) : null;
        if (source != null) {
            edges.add(callSite);
            setSource(edges.size() - 1, source);
        } else {
            edges.add(edge.getCallee() == this && callSite.isPlainEdge(edge)
                    ? callSite : edge);
        }
    }

    /**
     * Records {@code source} as the source of the edge at {@code index} of
     * {@link #edges}, the last one so far, in the form of {@link #sources}
     * that takes fewer bytes; a dense store grows as {@link ArrayList}
     * grows.
     */
    private void setSource(int index, EdgeSource source) {
        Object s = sources;
        if (s == null) {
            sources = index < SPARSE_MIN_INDEX
                    ? dense(index + 1, index, source)
                    : new SparseSources(index, source);
            return;
        }
        if (s instanceof SparseSources sparse) {
            // dense takes 4 bytes per index up to this one, sparse 8 per
            // sourced index
            if (2L * (sparse.count + 1) >= index + 1L) {
                EdgeSource[] dense = dense(index + 1, index, source);
                sparse.copyTo(dense);
                sources = dense;
            } else {
                sparse.add(index, source);
            }
            return;
        }
        EdgeSource[] dense = (EdgeSource[]) s;
        if (index >= dense.length) {
            int length = dense.length;
            dense = Arrays.copyOf(dense, Math.max(index + 1, length + (length >> 1)));
            sources = dense;
        }
        dense[index] = source;
    }

    /**
     * @return a dense store of {@code length} with {@code source} at
     * {@code index}.
     */
    private static EdgeSource[] dense(int length, int index, EdgeSource source) {
        EdgeSource[] dense = new EdgeSource[length];
        dense[index] = source;
        return dense;
    }

    /**
     * @return the source of the edge at {@code index} of {@link #edges}, or
     * null if it is not a sourced edge.
     */
    @Nullable
    private EdgeSource sourceAt(int index) {
        Object s = sources;
        if (s instanceof EdgeSource[] dense) {
            return index < dense.length ? dense[index] : null;
        }
        return s == null ? null : ((SparseSources) s).get(index);
    }

    /**
     * Adds the call sites of the edges to this CS method, and its sources,
     * to {@code census}: the number of sourced edges, the bytes of
     * {@link #sources} and the bytes of the shortest dense store.
     */
    @SuppressWarnings("unchecked")
    void census(EdgeSourceCensus census) {
        for (Object e : edges) {
            census.callSite(e instanceof CSCallSite callSite
                    ? callSite
                    : ((Edge<CSCallSite, CSMethod>) e).getCallSite());
        }
        Object s = sources;
        if (s == null) {
            return;
        }
        int sourced = 0;
        int last = -1;
        long bytes;
        if (s instanceof EdgeSource[] dense) {
            for (int i = 0; i < dense.length; ++i) {
                if (dense[i] != null) {
                    ++sourced;
                    last = i;
                }
            }
            bytes = EdgeSourceCensus.arrayBytes(dense.length, 4);
        } else {
            SparseSources sparse = (SparseSources) s;
            sourced = sparse.count;
            last = sparse.indices[sparse.count - 1];
            bytes = sparse.bytes();
        }
        census.callee(sourced, bytes, EdgeSourceCensus.arrayBytes(last + 1, 4));
    }

    /**
     * The sources of the sourced edges of a CS method with their indices
     * in {@link #edges}, by ascending index.
     */
    private static final class SparseSources {

        /**
         * Estimated bytes of the object itself: header and fields.
         */
        private static final int OBJECT_BYTES = 24;

        private int[] indices;

        private EdgeSource[] values;

        private int count;

        private SparseSources(int index, EdgeSource source) {
            indices = new int[] {index};
            values = new EdgeSource[] {source};
            count = 1;
        }

        /**
         * Adds {@code source} at {@code index}, above every index held.
         */
        private void add(int index, EdgeSource source) {
            if (count == indices.length) {
                int length = count + Math.max(1, count >> 1);
                indices = Arrays.copyOf(indices, length);
                values = Arrays.copyOf(values, length);
            }
            indices[count] = index;
            values[count] = source;
            ++count;
        }

        @Nullable
        private EdgeSource get(int index) {
            if (index > indices[count - 1]) {
                // the edges after the last sourced one, without a search
                return null;
            }
            int i = Arrays.binarySearch(indices, 0, count, index);
            return i >= 0 ? values[i] : null;
        }

        /**
         * Puts the sources at their indices of {@code dense}.
         */
        private void copyTo(EdgeSource[] dense) {
            for (int i = 0; i < count; ++i) {
                dense[indices[i]] = values[i];
            }
        }

        private long bytes() {
            return OBJECT_BYTES + EdgeSourceCensus.arrayBytes(indices.length, 4)
                    + EdgeSourceCensus.arrayBytes(values.length, 4);
        }
    }

    /**
     * @return an unmodifiable view of the call edges to this CS method, in
     * the order they were added; the view holds no duplicate edges and
     * shows the edges added later. A plain or sourced edge is rebuilt on
     * each read, so
     * the view returns equal, but not the same, edge objects across reads.
     */
    public List<Edge<CSCallSite, CSMethod>> getEdges() {
        return new EdgeView();
    }

    /**
     * @return the number of call edges to this CS method.
     */
    public int getEdgeCount() {
        return edges.size();
    }

    /**
     * @return the {@code i}-th call edge to this CS method, in the order
     * the edges were added.
     * @throws IndexOutOfBoundsException if {@code i} is not below
     *                                   {@link #getEdgeCount()}
     */
    public Edge<CSCallSite, CSMethod> getEdge(int i) {
        return expand(edges.get(i), i);
    }

    /**
     * @return the edge that the element {@code e} at {@code index} of
     * {@link #edges} holds.
     */
    @SuppressWarnings("unchecked")
    private Edge<CSCallSite, CSMethod> expand(Object e, int index) {
        EdgeSource source = sourceAt(index);
        if (source != null) {
            return source.edge((CSCallSite) e, this);
        }
        return e instanceof CSCallSite callSite
                ? callSite.plainEdgeTo(this)
                : (Edge<CSCallSite, CSMethod>) e;
    }

    /**
     * Unmodifiable live view of {@link #edges} as edges. Iteration, forEach
     * and spliterator go through the list's own, so they are fail-fast
     * against edges added meanwhile, as a view of the list itself is.
     */
    private final class EdgeView extends AbstractList<Edge<CSCallSite, CSMethod>>
            implements RandomAccess {

        @Override
        public Edge<CSCallSite, CSMethod> get(int index) {
            return getEdge(index);
        }

        @Override
        public int size() {
            return edges.size();
        }

        @Override
        public Iterator<Edge<CSCallSite, CSMethod>> iterator() {
            Iterator<Object> it = edges.iterator();
            return new Iterator<>() {

                private int index;

                @Override
                public boolean hasNext() {
                    return it.hasNext();
                }

                @Override
                public Edge<CSCallSite, CSMethod> next() {
                    Object e = it.next();
                    return expand(e, index++);
                }
            };
        }

        @Override
        public void forEach(Consumer<? super Edge<CSCallSite, CSMethod>> action) {
            int[] index = {0};
            edges.forEach(e -> action.accept(expand(e, index[0]++)));
        }

        @Override
        public Spliterator<Edge<CSCallSite, CSMethod>> spliterator() {
            return new ExpandingSpliterator(edges.spliterator(), 0);
        }
    }

    /**
     * Spliterator over {@link #edges} as edges; late-binding and fail-fast
     * as the list's own. It tracks the index of its next element, which
     * locates the element's source: the list's spliterator is sized and
     * splits off a prefix of exactly its estimated size.
     */
    private final class ExpandingSpliterator
            implements Spliterator<Edge<CSCallSite, CSMethod>> {

        private final Spliterator<Object> source;

        private int index;

        private ExpandingSpliterator(Spliterator<Object> source, int index) {
            this.source = source;
            this.index = index;
        }

        @Override
        public boolean tryAdvance(Consumer<? super Edge<CSCallSite, CSMethod>> action) {
            return source.tryAdvance(e -> action.accept(expand(e, index++)));
        }

        @Override
        public void forEachRemaining(Consumer<? super Edge<CSCallSite, CSMethod>> action) {
            source.forEachRemaining(e -> action.accept(expand(e, index++)));
        }

        @Override
        public Spliterator<Edge<CSCallSite, CSMethod>> trySplit() {
            Spliterator<Object> prefix = source.trySplit();
            if (prefix == null) {
                return null;
            }
            ExpandingSpliterator split = new ExpandingSpliterator(prefix, index);
            index += (int) prefix.estimateSize();
            return split;
        }

        @Override
        public long estimateSize() {
            return source.estimateSize();
        }

        @Override
        public int characteristics() {
            return source.characteristics();
        }
    }

    public <R> R getResult(String id, Supplier<R> supplier) {
        return resultHolder.getResult(id, supplier);
    }

    public <R> Optional<R> getResult(String id) {
        return Optional.ofNullable(resultHolder.getResult(id));
    }

    /**
     * @return the exception analysis's result on this CS method, or null
     * if that analysis propagated no exception here yet.
     */
    public CSMethodThrowResult getThrowResult() {
        return throwResult;
    }

    /**
     * Sets the exception analysis's result on this CS method; for that
     * analysis, once per CS method.
     */
    public void setThrowResult(CSMethodThrowResult throwResult) {
        this.throwResult = throwResult;
    }

    @Override
    public String toString() {
        return context + ":" + method;
    }
}
