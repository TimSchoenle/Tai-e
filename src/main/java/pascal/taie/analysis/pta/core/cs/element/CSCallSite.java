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
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.util.collection.SetEx;

import java.util.Collections;
import java.util.Set;

/**
 * Represents context-sensitive call sites.
 */
public class CSCallSite extends AbstractCSElement {

    private final Invoke callSite;

    /**
     * Context-sensitive method which contains this CS call site.
     */
    private final CSMethod container;

    /**
     * Call edges from this call site.
     */
    private final CallSiteEdges edges;

    /**
     * Exceptions that the exception analysis found this call site may
     * throw; null until it finds the first.
     */
    private SetEx<CSObj> thrownExceptions;

    CSCallSite(Invoke callSite, Context context, CSMethod container) {
        super(context);
        this.callSite = callSite;
        this.container = container;
        this.edges = new CallSiteEdges(this,
                callSite == null ? null : CallGraphs.findCallKind(callSite));
    }

    /**
     * @return the call site (without context).
     */
    public Invoke getCallSite() {
        return callSite;
    }

    public CSMethod getContainer() {
        return container;
    }

    public boolean addEdge(Edge<CSCallSite, CSMethod> edge) {
        return edges.add(edge);
    }

    /**
     * @return whether this call site already has the edge
     * {@code new Edge<>(kind, this, callee)}, checked without allocating
     * it. Answers false (unknown) unless {@code kind} is this call site's
     * own kind, {@link CallGraphs#findCallKind(Invoke)}.
     */
    public boolean hasPlainEdge(CallKind kind, CSMethod callee) {
        return edges.containsPlain(kind, callee);
    }

    /**
     * @return whether this call site already has the sourced edge
     * {@code source.edge(this, callee)}, checked without allocating it.
     */
    public boolean hasSourcedEdge(EdgeSource source, CSMethod callee) {
        return edges.containsSourced(source, callee);
    }

    /**
     * @return a live, unmodifiable view of the call edges from this call
     * site. A plain edge (of class {@link Edge}, of this call site's own
     * kind) and a {@link SourcedEdge} are held without their objects and
     * rebuilt on each read, so the view returns equal, but not the same,
     * edge objects across reads.
     */
    public Set<Edge<CSCallSite, CSMethod>> getEdges() {
        return Collections.unmodifiableSet(edges);
    }

    /**
     * @return whether {@code edge} is a plain edge of this call site, which
     * {@link CSMethod} holds as the call site alone.
     */
    boolean isPlainEdge(Edge<CSCallSite, CSMethod> edge) {
        return edges.isPlain(edge);
    }

    /**
     * @return the source of {@code edge} if it is a sourced edge of this
     * call site, which {@link CSMethod} holds as the call site and the
     * source; otherwise null.
     */
    @Nullable
    EdgeSource sourceOf(Edge<CSCallSite, CSMethod> edge) {
        return edges.sourceOf(edge);
    }

    /**
     * @return a new plain edge from this call site to {@code callee}.
     */
    Edge<CSCallSite, CSMethod> plainEdgeTo(CSMethod callee) {
        return edges.plainEdge(callee);
    }

    /**
     * @return the live set of exceptions that the exception analysis found
     * this call site may throw, or null if it found none yet; only that
     * analysis changes it.
     */
    public SetEx<CSObj> getThrownExceptions() {
        return thrownExceptions;
    }

    /**
     * Sets the set of exceptions this call site may throw; for the
     * exception analysis, once per call site.
     */
    public void setThrownExceptions(SetEx<CSObj> thrownExceptions) {
        this.thrownExceptions = thrownExceptions;
    }

    @Override
    public String toString() {
        return context + ":" + callSite;
    }
}
