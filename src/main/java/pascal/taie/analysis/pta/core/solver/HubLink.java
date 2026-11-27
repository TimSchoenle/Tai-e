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

import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;

import java.util.Arrays;

/**
 * A work-list entry of option {@code call-hubs}: the callee nodes that one
 * batch of a call site offered fresh (not linked from the call site at the
 * offer), in first-offer order and distinct. It is queued at the batch's
 * first fresh offer, where that offer's call edge would be queued, and the
 * batch appends the rest. At its poll the solver links the nodes still not
 * linked: one alone as a stored edge, two or more through a call hub.
 */
final class HubLink {

    private final CSCallSite site;

    private CSMethod[] nodes = new CSMethod[4];

    private int size;

    HubLink(CSCallSite site) {
        this.site = site;
    }

    CSCallSite site() {
        return site;
    }

    /**
     * Appends a node; the batch offers each node once.
     */
    void add(CSMethod node) {
        if (size == nodes.length) {
            nodes = Arrays.copyOf(nodes, size * 2);
        }
        nodes[size++] = node;
    }

    int size() {
        return size;
    }

    CSMethod node(int i) {
        return nodes[i];
    }
}
