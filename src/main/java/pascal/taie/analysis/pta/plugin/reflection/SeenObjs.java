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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.stmt.Invoke;

import java.util.List;

/**
 * The objects of one argument of one handler call site (one variable in one
 * context) that the handler has taken already.
 * <p>
 * {@code AnalysisModelPlugin} calls a handler with the new objects of the
 * variable that changed and with the whole current points-to set of every
 * other argument, the very set object the solver holds. A handler that
 * pairs two arguments must not cross both whole sets again on every change:
 * {@link #unseen} returns only what it has not taken, and skips the whole
 * set without a scan when every object of it has been taken.
 */
final class SeenObjs {

    private final PointsToSet seen;

    /**
     * @param empty a new, empty, unshared points-to set, owned by this object
     */
    SeenObjs(PointsToSet empty) {
        this.seen = empty;
    }

    /**
     * Takes the objects of {@code given} that no earlier call gave.
     *
     * @param given a set the handler got for the variable: its new objects,
     *              or its whole current points-to set
     * @param live  the variable's current points-to set, as the solver holds it
     * @return the objects of {@code given} not taken before
     */
    Iterable<CSObj> unseen(PointsToSet given, PointsToSet live) {
        // everything taken came from this variable, whose set only grows,
        // so the taken objects are a subset of the live set: equal sizes
        // mean equal sets
        if (given == live && live.size() == seen.size()) {
            return List.of();
        }
        return seen.addAllDiff(given);
    }

    /**
     * @return the current points-to set of argument {@code index} of
     * {@code invoke} in {@code context}, the set object the solver holds
     * and hands to the handlers.
     */
    static PointsToSet livePointsTo(Solver solver, Context context, Invoke invoke, int index) {
        return solver.getPointsToSetOf(solver.getCSManager()
                .getCSVar(context, InvokeUtils.getVar(invoke, index)));
    }
}
