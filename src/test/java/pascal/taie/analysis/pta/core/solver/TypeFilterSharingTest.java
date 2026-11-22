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

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.util.collection.Sets;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The solver gives all edges with the same guard type one type filter.
 */
class TypeFilterSharingTest {

    private static int typeFilterTransfers;

    private static int filtersByType;

    private static int filtersByIdentity;

    /**
     * Counts the type filters on the pointer flow graph when the solver
     * finishes. Public with a no-argument constructor: the analysis loads
     * it by name.
     */
    public static class CountFilters implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            Set<Transfer> byType = Sets.newSet();
            Set<Transfer> byIdentity = Collections.newSetFromMap(new IdentityHashMap<>());
            int[] count = new int[1];
            solver.getCSManager().pointers().forEach((Pointer p) ->
                    p.getOutEdges().forEach(edge -> edge.forEachTransfer(t -> {
                        if (t instanceof TypeFilter) {
                            count[0]++;
                            byType.add(t);
                            byIdentity.add(t);
                        }
                    })));
            typeFilterTransfers = count[0];
            filtersByType = byType.size();
            filtersByIdentity = byIdentity.size();
        }
    }

    @Test
    void edgesWithTheSameGuardTypeShareOneFilter() {
        typeFilterTransfers = 0;
        filtersByType = 0;
        filtersByIdentity = 0;
        Main.main("-cp", "src/test/resources/pta/basic", "-m", "Cast2",
                "-a", "pta=only-app:true;implicit-entries:false;plugins:["
                        + CountFilters.class.getName() + "]");
        assertTrue(typeFilterTransfers > filtersByType,
                "the program must have two edges with the same guard type: "
                        + typeFilterTransfers + " filters, " + filtersByType + " types");
        assertEquals(filtersByType, filtersByIdentity);
    }
}
