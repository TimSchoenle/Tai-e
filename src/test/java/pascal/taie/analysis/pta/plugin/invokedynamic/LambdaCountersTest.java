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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.heap.MockObj;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lambda analysis' counters count what they name.
 */
class LambdaCountersTest {

    private final TrieContext.Factory<String> contexts = new TrieContext.Factory<>();

    private final Context empty = contexts.getEmptyContext();

    private final Context other = contexts.make("c");

    @Test
    void countsEntersAndHitsPerPath() {
        LambdaCounters c = new LambdaCounters();
        c.enter(LambdaCounters.PATH_CALL, true);
        c.enter(LambdaCounters.PATH_CALL, false);
        c.enter(LambdaCounters.PATH_SHARED, true);
        assertEquals(2, c.enters(LambdaCounters.PATH_CALL));
        assertEquals(1, c.enterHits(LambdaCounters.PATH_CALL));
        assertEquals(0, c.enters(LambdaCounters.PATH_NEW_PTS));
        assertEquals(1, c.enterHits(LambdaCounters.PATH_SHARED));
    }

    @Test
    void countsRepeatedThisUpdatesPerEventAndCallee() {
        LambdaCounters c = new LambdaCounters();
        c.startEvent();
        c.thisUpdate(empty, null);
        c.thisUpdate(other, null);
        c.thisUpdate(empty, null);
        c.startEvent();
        c.thisUpdate(empty, null);
        assertEquals(4, c.thisUpdates());
        assertEquals(1, c.repeatedThisUpdates());
    }

    @Test
    void countsEdgesAndTheInfosHistogram() {
        LambdaCounters c = new LambdaCounters();
        c.edgeBuilt();
        c.edgeBuilt();
        c.edgeNew();
        assertEquals(2, c.edgesBuilt());
        assertEquals(1, c.edgesNew());
        String line = c.line(List.of(1, 1, 3));
        assertTrue(line.startsWith("enter_call=0/0 enter_new_pts=0/0 enter_shared=0/0 "), line);
        assertTrue(line.contains(" edges_built=2 edges_new=1 receiver_vars=3 "), line);
    }

    @Test
    void tellsOnlyItsOwnLambdaObjects() {
        assertFalse(LambdaAnalysis.isLambdaObj(
                new MockObj(() -> "LambdaObj", "indy", null, null, true)));
    }
}
