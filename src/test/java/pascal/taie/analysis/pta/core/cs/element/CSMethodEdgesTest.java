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

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The incoming edges of a CS method are read as a list view and by index,
 * without a copy.
 */
public class CSMethodEdgesTest {

    private final Context context = new TrieContext.Factory<>().getEmptyContext();

    private final CSMethod callee = new CSMethod(null, context);

    @Test
    void edgesAreAViewInInsertionOrder() {
        List<Edge<CSCallSite, CSMethod>> view = callee.getEdges();
        Edge<CSCallSite, CSMethod> first = edge();
        Edge<CSCallSite, CSMethod> second = edge();
        callee.addEdge(first);
        callee.addEdge(second);
        assertEquals(List.of(first, second), view);
        assertEquals(2, callee.getEdgeCount());
        assertSame(first, callee.getEdge(0));
        assertSame(second, callee.getEdge(1));
    }

    @Test
    void edgesCannotBeChangedThroughTheView() {
        callee.addEdge(edge());
        List<Edge<CSCallSite, CSMethod>> view = callee.getEdges();
        assertThrows(UnsupportedOperationException.class, () -> view.add(edge()));
        assertThrows(UnsupportedOperationException.class, () -> view.remove(0));
        assertEquals(1, callee.getEdgeCount());
    }

    private Edge<CSCallSite, CSMethod> edge() {
        CSCallSite site = new CSCallSite(null, context, new CSMethod(null, context));
        return new Edge<>(CallKind.STATIC, site, callee);
    }
}
