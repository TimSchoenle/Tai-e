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

package pascal.taie.analysis.pta;

import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;

import java.util.ArrayList;
import java.util.List;

/**
 * Records, in the order the solver reports them, every new
 * context-sensitive method, every new call edge and every new points-to
 * set of every variable with its objects in iteration order.
 */
public class SolverOrderRecorder implements Plugin {

    static final List<String> EVENTS = new ArrayList<>();

    @Override
    public void onStart() {
        EVENTS.clear();
    }

    @Override
    public void onNewCSMethod(CSMethod csMethod) {
        EVENTS.add("method " + csMethod);
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        EVENTS.add("edge " + edge);
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        StringBuilder line = new StringBuilder("pts ").append(csVar);
        for (CSObj obj : pts) {
            line.append(' ').append(obj);
        }
        EVENTS.add(line.toString());
    }
}
