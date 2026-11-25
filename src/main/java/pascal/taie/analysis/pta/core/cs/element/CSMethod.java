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
     * The sources of the sourced edges, at their indices in {@link #edges};
     * null at the other indices, and may be shorter than {@link #edges}.
     * Null while no sourced edge was added.
     */
    private EdgeSource @Nullable [] sources;

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
     * {@link #edges}, growing {@link #sources} as {@link ArrayList} grows.
     */
    private void setSource(int index, EdgeSource source) {
        if (sources == null) {
            sources = new EdgeSource[index + 1];
        } else if (index >= sources.length) {
            int length = sources.length;
            sources = Arrays.copyOf(sources, Math.max(index + 1, length + (length >> 1)));
        }
        sources[index] = source;
    }

    /**
     * @return the source of the edge at {@code index} of {@link #edges}, or
     * null if it is not a sourced edge.
     */
    @Nullable
    private EdgeSource sourceAt(int index) {
        EdgeSource[] s = sources;
        return s != null && index < s.length ? s[index] : null;
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
