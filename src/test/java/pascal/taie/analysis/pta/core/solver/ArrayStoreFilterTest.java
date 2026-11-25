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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.util.collection.Maps;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The new array store edges of one array variable's delta that carry the
 * same type filter share one application of it to the stored variable's
 * points-to set, instead of one application per array.
 */
class ArrayStoreFilterTest {

    /**
     * Per guard type name: array store edges carrying its filter, its
     * applications.
     */
    private static final Map<String, long[]> EDGES_AND_APPLICATIONS = Maps.newMap();

    /**
     * Per array object: the types of the objects stored into it.
     */
    private static final List<String> STORED = new ArrayList<>();

    /**
     * Records the counts at the end of the analysis. Public with a
     * no-argument constructor: the analysis loads it by name.
     */
    public static class Record implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            solver.getCSManager().pointers().forEach((Pointer p) ->
                    p.getOutEdges().forEach(edge -> {
                        if (edge.kind() == FlowKind.ARRAY_STORE) {
                            edge.forEachTransfer(t -> {
                                if (t instanceof TypeFilter filter) {
                                    String guard = ((ArrayIndex) edge.target())
                                            .getType().getName();
                                    long[] counts = EDGES_AND_APPLICATIONS
                                            .computeIfAbsent(guard, g -> new long[2]);
                                    counts[0]++;
                                    counts[1] = filter.applications();
                                }
                            });
                        }
                    }));
            solver.getCSManager().getArrayIndexes().forEach(index -> {
                String array = index.getArray().getObject().getType().getName();
                if (!array.equals("A[]") && !array.equals("B[]")) {
                    return;
                }
                List<String> stored = new ArrayList<>();
                for (CSObj o : solver.getPointsToSetOf(index)) {
                    stored.add(o.getObject().getType().getName());
                }
                STORED.add(array + ": " + stored.stream().sorted()
                        .collect(Collectors.joining(" ")));
            });
        }
    }

    @BeforeAll
    static void analyze() {
        Main.main("-cp", "src/test/resources/pta/arraystore", "-m", "ArrayStore",
                "-a", "pta=only-app:true;implicit-entries:false;plugins:["
                        + Record.class.getName() + "]");
    }

    @Test
    void eachFilterIsAppliedOncePerArrayDelta() {
        // the eight arrays reach arr in one delta, after x and z got their
        // objects (they are pending before arr is): per filter and stored
        // variable one application for its four new edges, not one per edge
        assertEquals("A=8/2 B=8/2", counts());
    }

    @Test
    void everyArrayGetsTheObjectsItsElementTypeAdmits() {
        assertEquals(List.of("A[]: A B", "A[]: A B", "A[]: A B", "A[]: A B",
                "B[]: B", "B[]: B", "B[]: B", "B[]: B"), STORED.stream().sorted().toList());
    }

    private static String counts() {
        return EDGES_AND_APPLICATIONS.entrySet().stream()
                .sorted(Map.Entry.comparingByKey())
                .map(e -> e.getKey() + "=" + e.getValue()[0] + "/" + e.getValue()[1])
                .collect(Collectors.joining(" "));
    }
}
