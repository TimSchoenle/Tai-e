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

package pascal.taie.analysis.pta.plugin.reflection;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.TestElements;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Checks that {@link SeenObjs} hands each object of a growing variable to
 * the handler once, whether it arrives as a delta or only in the whole set,
 * and skips the whole set when every object of it was taken.
 */
class SeenObjsTest {

    private final CSObj[] objs = TestElements.objects(8);

    private final PointsToSetFactory factory =
            new PointsToSetFactory(TestElements.indexer(objs));

    @Test
    void deltasOnceAndTheWholeSetSkippedWhenAllTaken() {
        PointsToSet live = factory.make();
        SeenObjs seen = new SeenObjs(factory.make());
        assertEquals(List.of(), list(seen.unseen(live, live)));
        for (int i = 0; i < 4; i++) {
            PointsToSet delta = factory.make();
            delta.addObject(objs[i]);
            live.addObject(objs[i]);
            assertEquals(List.of(objs[i]), list(seen.unseen(delta, live)));
            assertEquals(List.of(), list(seen.unseen(live, live)));
        }
    }

    @Test
    void anObjectThatCameOnlyInTheWholeSetIsTakenOnce() {
        PointsToSet live = factory.make();
        SeenObjs seen = new SeenObjs(factory.make());
        live.addObject(objs[0]);
        live.addObject(objs[1]);
        assertEquals(List.of(objs[0], objs[1]), list(seen.unseen(live, live)));
        assertEquals(List.of(), list(seen.unseen(live, live)));
        // a copy of the whole set is not the live set: scanned, nothing new
        assertEquals(List.of(), list(seen.unseen(live.copy(), live)));
    }

    private static List<CSObj> list(Iterable<CSObj> objs) {
        List<CSObj> list = new ArrayList<>();
        objs.forEach(list::add);
        return list;
    }
}
