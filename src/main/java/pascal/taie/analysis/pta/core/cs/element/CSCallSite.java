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

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.NoSuchElementException;
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
     * The call hubs this call site is a member of (option
     * {@code call-hubs}), in join order; null if none.
     */
    private CallHub @Nullable [] hubs;

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

    /**
     * Adds a stored edge; refuses a plain edge that one of the call
     * site's hubs already holds.
     */
    public boolean addEdge(Edge<CSCallSite, CSMethod> edge) {
        if (hubs != null && edges.isPlain(edge) && hubsContain(edge.getCallee())) {
            return false;
        }
        return edges.add(edge);
    }

    /**
     * @return whether this call site already has the edge
     * {@code new Edge<>(kind, this, callee)}, stored or in one of its hubs
     * (announced or not), checked without allocating it. Answers false
     * (unknown) unless {@code kind} is this call site's own kind,
     * {@link CallGraphs#findCallKind(Invoke)}.
     */
    public boolean hasPlainEdge(CallKind kind, CSMethod callee) {
        if (edges.containsPlain(kind, callee)) {
            return true;
        }
        return hubs != null && kind == CallGraphs.findCallKind(callSite) && hubsContain(callee);
    }

    /**
     * @return whether one of the hubs of this call site has {@code callee}
     * as a target
     */
    private boolean hubsContain(CSMethod callee) {
        for (CallHub hub : hubs) {
            if (hub.contains(callee)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return whether a plain edge to {@code callee} of kind {@code kind}
     * could be held by a hub of this call site: {@code kind} is the call
     * site's own kind
     */
    public boolean isOwnPlainKind(CallKind kind) {
        return callSite != null && kind == CallGraphs.findCallKind(callSite);
    }

    /**
     * @return the number of hubs this call site is a member of
     */
    public int getHubCount() {
        return hubs == null ? 0 : hubs.length;
    }

    /**
     * Appends {@code hub}; for {@link CallHub#beginJoin} only.
     */
    void addHub(CallHub hub) {
        CallHub[] old = hubs;
        if (old == null) {
            hubs = new CallHub[] {hub};
        } else {
            CallHub[] grown = Arrays.copyOf(old, old.length + 1);
            grown[old.length] = hub;
            hubs = grown;
        }
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
        return hubs == null ? Collections.unmodifiableSet(edges) : new HubbedEdges();
    }

    /**
     * The edges of a call site with hubs: the stored edges, then per hub
     * its targets announced to this call site, in hub order. Hub targets
     * are disjoint from the stored plain edges and from each other.
     */
    private final class HubbedEdges extends AbstractSet<Edge<CSCallSite, CSMethod>> {

        @Override
        public int size() {
            int size = edges.size();
            for (CallHub hub : hubs) {
                size += hub.visibleTargets(CSCallSite.this);
            }
            return size;
        }

        @Override
        public boolean contains(Object o) {
            if (edges.contains(o)) {
                return true;
            }
            if (!(o instanceof Edge<?, ?> edge) || !edges.isPlain(edge)
                    || !(edge.getCallee() instanceof CSMethod callee)) {
                return false;
            }
            for (CallHub hub : hubs) {
                int i = hub.indexOf(callee);
                if (i >= 0) {
                    return i < hub.visibleTargets(CSCallSite.this);
                }
            }
            return false;
        }

        @Override
        public Iterator<Edge<CSCallSite, CSMethod>> iterator() {
            Iterator<Edge<CSCallSite, CSMethod>> stored = edges.iterator();
            CallHub[] refs = hubs;
            return new Iterator<>() {
                private int hubIndex;
                private int target;

                @Override
                public boolean hasNext() {
                    if (stored.hasNext()) {
                        return true;
                    }
                    while (hubIndex < refs.length) {
                        if (target < refs[hubIndex].visibleTargets(CSCallSite.this)) {
                            return true;
                        }
                        ++hubIndex;
                        target = 0;
                    }
                    return false;
                }

                @Override
                public Edge<CSCallSite, CSMethod> next() {
                    if (stored.hasNext()) {
                        return stored.next();
                    }
                    if (!hasNext()) {
                        throw new NoSuchElementException();
                    }
                    return refs[hubIndex].edge(CSCallSite.this, target++);
                }
            };
        }
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
     * Adds the sources of the edges from this call site to {@code census}.
     */
    void census(EdgeSourceCensus census) {
        edges.census(census);
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
