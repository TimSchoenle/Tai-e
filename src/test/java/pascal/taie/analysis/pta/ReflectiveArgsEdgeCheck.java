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

import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

/**
 * Checks the shape of reflective argument passing at the end of the analysis:
 * the elements of an argument array flow into the callee parameters through
 * at most one parameter-passing edge per array, however many reflective
 * callees and parameters receive them.
 */
public class ReflectiveArgsEdgeCheck implements Plugin {

    private Solver solver;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
    }

    @Override
    public void onFinish() {
        long passingArrays = solver.getCSManager().pointers()
                .filter(p -> p instanceof ArrayIndex)
                .filter(p -> {
                    long passing = p.getOutEdges().stream()
                            .map(PointerFlowEdge::kind)
                            .filter(k -> k == FlowKind.PARAMETER_PASSING)
                            .count();
                    if (passing > 1) {
                        throw new AssertionError(p + " has " + passing
                                + " parameter-passing edges, expected at most one");
                    }
                    return passing == 1;
                })
                .count();
        if (passingArrays == 0) {
            throw new AssertionError("no argument array passes its elements");
        }
    }
}
