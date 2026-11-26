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

import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.util.Indexer;

/**
 * Context-sensitive objects and pointers for unit tests that need no world.
 */
public final class TestElements {

    private TestElements() {
    }

    /**
     * @return {@code n} objects whose indexes are their positions.
     */
    public static CSObj[] objects(int n) {
        TrieContext context = new TrieContext.Factory<>().getEmptyContext();
        CSObj[] objs = new CSObj[n];
        for (int i = 0; i < n; ++i) {
            String name = "o" + i;
            objs[i] = new CSObj(new MockObj(() -> name, name, null, null, false), context, i);
        }
        return objs;
    }

    /**
     * @return {@code obj} in the empty context, with index {@code index}.
     */
    public static CSObj object(Obj obj, int index) {
        return new CSObj(obj, new TrieContext.Factory<>().getEmptyContext(), index);
    }

    /**
     * @return the indexer of objects made by {@link #objects(int)}.
     */
    public static Indexer<CSObj> indexer(CSObj[] objs) {
        return new Indexer<>() {
            @Override
            public int getIndex(CSObj o) {
                return o.getIndex();
            }

            @Override
            public CSObj getObject(int index) {
                return objs[index];
            }
        };
    }

    /**
     * @return a pointer without points-to set.
     */
    public static Pointer pointer(int index) {
        String name = "p" + index;
        return new MockPointer(() -> name, name, null, index);
    }
}
