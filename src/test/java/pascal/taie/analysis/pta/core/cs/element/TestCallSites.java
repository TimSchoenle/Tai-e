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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.ir.exp.Var;

/**
 * Test factory of context-sensitive call sites and variables without a call
 * site, a container or a method, for tests that only need distinct
 * identities.
 */
public final class TestCallSites {

    private TestCallSites() {
    }

    public static CSCallSite detached(Context context) {
        return new CSCallSite(null, context, null);
    }

    /**
     * @return a context-sensitive variable of a variable without a method
     * or a type: distinct calls give distinct (identity-equal) variables.
     */
    public static CSVar detachedVar(Context context, int index) {
        return new CSVar(new Var(null, "v" + index, null, index), context, index);
    }
}
