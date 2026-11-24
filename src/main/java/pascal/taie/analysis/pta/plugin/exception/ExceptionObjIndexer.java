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

package pascal.taie.analysis.pta.plugin.exception;

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.util.Indexer;

import java.util.Arrays;

/**
 * Numbers the exception objects 0..n-1 in the order in which exception
 * analysis first sees them, so that a bit set of exception objects is as
 * wide as the number of distinct exception objects, not as the global
 * index of its highest {@link CSObj}.
 * <p>
 * An object gets its local index on the first {@link #getIndex} call.
 * Sets over this indexer and sets over the global {@link CSObj} indexer
 * must never be combined word-wise.
 */
final class ExceptionObjIndexer implements Indexer<CSObj> {

    /**
     * Initial length of {@link #localByGlobal}.
     */
    private static final int INITIAL_GLOBAL_CAPACITY = 1024;

    /**
     * Initial length of {@link #objs}.
     */
    private static final int INITIAL_LOCAL_CAPACITY = 64;

    /**
     * Maps the global index of a {@link CSObj} to its local index plus one;
     * 0 marks an object without a local index.
     */
    private int[] localByGlobal = new int[INITIAL_GLOBAL_CAPACITY];

    /**
     * Maps each local index to its object.
     */
    private CSObj[] objs = new CSObj[INITIAL_LOCAL_CAPACITY];

    private int size;

    @Override
    public int getIndex(CSObj o) {
        int global = o.getIndex();
        if (global >= localByGlobal.length) {
            localByGlobal = Arrays.copyOf(localByGlobal,
                    Math.max(global + 1, 2 * localByGlobal.length));
        }
        int localPlusOne = localByGlobal[global];
        if (localPlusOne == 0) {
            if (size == objs.length) {
                objs = Arrays.copyOf(objs, 2 * objs.length);
            }
            objs[size] = o;
            localPlusOne = ++size;
            localByGlobal[global] = localPlusOne;
        }
        return localPlusOne - 1;
    }

    @Override
    public CSObj getObject(int index) {
        return objs[index];
    }

    /**
     * @return the number of objects that have a local index.
     */
    int size() {
        return size;
    }
}
