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

import pascal.taie.analysis.graph.callgraph.Edge;

/**
 * What a call edge carries beyond its call site and callee, shared by many
 * edges. A {@link CSCallSite} and a {@link CSMethod} hold a
 * {@link SourcedEdge} as its source alone (beside the callee, respectively
 * the call site) and rebuild the edge with {@link #edge} on each read.
 * <p>
 * Contract, for every call site {@code s} and callee {@code m}:
 * {@code edge(s, m)} is a {@link SourcedEdge} whose source equals this
 * source, from {@code s} to {@code m}, and its hash code is
 * {@code edgeHashCode(s, m)}; two such edges {@code a.edge(s, m)} and
 * {@code b.edge(s, m)} are equal exactly when {@code a.equals(b)}; and such
 * an edge never equals an edge that is not a {@link SourcedEdge}.
 */
public interface EdgeSource {

    /**
     * @return a new edge of this source from {@code callSite} to
     * {@code callee}.
     */
    Edge<CSCallSite, CSMethod> edge(CSCallSite callSite, CSMethod callee);

    /**
     * @return the hash code of {@link #edge edge(callSite, callee)},
     * without creating the edge.
     */
    int edgeHashCode(CSCallSite callSite, CSMethod callee);
}
