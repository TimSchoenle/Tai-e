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
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The solver applies each type filter once per propagated delta, not once
 * per out-edge that carries it; a type filter returns a large input whose
 * objects all pass as the result itself.
 */
class FanOutFilterTest {

    /**
     * Per type filter on the pointer flow graph: edges carrying it, its
     * applications.
     */
    private static final List<long[]> EDGES_AND_APPLICATIONS = new ArrayList<>();

    /**
     * Objects of type A and B in solver order, the filter results for guard
     * types A and B, and the size of the input after filtering.
     */
    private static final List<CSObj> INPUT = new ArrayList<>();

    private static final List<CSObj> B_OBJECTS = new ArrayList<>();

    private static PointsToSet input;

    private static PointsToSet passAll;

    private static PointsToSet passSome;

    private static int inputSizeAfter;

    /**
     * Records the counts and filters a large set at the end of the
     * analysis. Public with a no-argument constructor: the analysis loads
     * it by name.
     */
    public static class Record implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            Map<TypeFilter, long[]> edges = new IdentityHashMap<>();
            solver.getCSManager().pointers().forEach((Pointer p) ->
                    p.getOutEdges().forEach(edge -> edge.forEachTransfer(t -> {
                        if (t instanceof TypeFilter filter) {
                            edges.computeIfAbsent(filter, f -> new long[1])[0]++;
                        }
                    })));
            edges.forEach((filter, count) -> EDGES_AND_APPLICATIONS.add(
                    new long[]{count[0], filter.applications()}));

            input = solver.makePointsToSet();
            for (CSObj o : solver.getCSManager().getObjects()) {
                String name = o.getObject().getType().getName();
                if (name.equals("A") || name.equals("B")) {
                    input.addObject(o);
                }
            }
            input.forEach(o -> {
                INPUT.add(o);
                if (o.getObject().getType().getName().equals("B")) {
                    B_OBJECTS.add(o);
                }
            });
            var types = solver.getTypeSystem();
            passAll = new TypeFilter(types.getClassType("A"), solver).apply(null, input);
            passSome = new TypeFilter(types.getClassType("B"), solver).apply(null, input);
            inputSizeAfter = input.size();
        }
    }

    @BeforeAll
    static void analyze() {
        Main.main("-cp", "src/test/resources/pta/fan", "-m", "FanOut",
                "-a", "pta=only-app:true;implicit-entries:false;plugins:["
                        + Record.class.getName() + "]");
    }

    @Test
    void eachFilterIsAppliedOncePerDelta() {
        assertEquals(2, EDGES_AND_APPLICATIONS.size(), "filters for A and B");
        for (long[] counts : EDGES_AND_APPLICATIONS) {
            long edges = counts[0];
            long applications = counts[1];
            assertTrue(edges >= 4, "the fixture needs at least 4 edges per filter, has " + edges);
            // one application when each edge is added (on the empty source),
            // one for the single delta of the source pointer
            assertEquals(edges + 1, applications,
                    applications + " applications for " + edges + " edges and one delta");
        }
    }

    @Test
    void largeInputWhoseObjectsAllPassIsTheResult() {
        assertTrue(TypeFilter.representation(input) == 2,
                "the input must be held in a bit set, has " + INPUT.size() + " objects");
        assertSame(input, passAll);
    }

    @Test
    void largeInputWithFailingObjectsIsCopiedAndKept() {
        assertNotSame(input, passSome);
        assertEquals(INPUT.size(), inputSizeAfter);
        assertEquals(B_OBJECTS, new ArrayList<>(passSome.getObjects()));
        assertTrue(B_OBJECTS.size() < INPUT.size());
    }
}
