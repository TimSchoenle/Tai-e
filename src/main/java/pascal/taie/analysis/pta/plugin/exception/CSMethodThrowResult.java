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

import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.ir.proginfo.ExceptionEntry;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.SetEx;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

public class CSMethodThrowResult {

    private final Supplier<SetEx<CSObj>> setFactory;

    private final Map<Stmt, SetEx<CSObj>> explicitExceptions;

    private final SetEx<CSObj> uncaughtExceptions;

    /**
     * The exception entries of the method; null when it has none.
     */
    private final Catchers catchers;

    /**
     * The exception entries that may catch what each statement of a method
     * throws, indexed by statement index.
     *
     * @param stmts   the statements of the method's IR
     * @param byIndex for each statement index, the entries that cover the
     *                statement, in the order of the exception table, or
     *                null if none does
     */
    record Catchers(List<Stmt> stmts, ExceptionEntry[][] byIndex) {

        /**
         * @return the entries that cover {@code stmt}, or null if none does
         * or {@code stmt} is not a statement of the method's IR (such as a
         * synthetic call site)
         */
        ExceptionEntry[] of(Stmt stmt) {
            int index = stmt.getIndex();
            if (index < 0 || index >= byIndex.length) {
                return null;
            }
            ExceptionEntry[] entries = byIndex[index];
            return entries != null && stmts.get(index) == stmt ? entries : null;
        }
    }

    CSMethodThrowResult(Supplier<SetEx<CSObj>> setFactory, Catchers catchers) {
        this.setFactory = setFactory;
        this.catchers = catchers;
        explicitExceptions = Maps.newHybridMap();
        uncaughtExceptions = setFactory.get();
    }

    /**
     * @return the exception entries that may catch what {@code stmt}
     * throws, in the order of the method's exception table, or null if
     * none does
     */
    ExceptionEntry[] catchersOf(Stmt stmt) {
        return catchers == null ? null : catchers.of(stmt);
    }

    /**
     * Adds the exceptions to those that {@code callSite}, a call site of
     * this result's method, may throw; the set lives on the call site, so
     * that a later visit reads it without a map probe.
     *
     * @return the exceptions that are new to the call site; a shared
     * empty set when none is new
     */
    Set<CSObj> propagate(CSCallSite callSite, Set<CSObj> exceptions) {
        SetEx<CSObj> thrown = callSite.getThrownExceptions();
        if (thrown == null) {
            thrown = setFactory.get();
            callSite.setThrownExceptions(thrown);
            explicitExceptions.put(callSite.getCallSite(), thrown);
        } else if (thrown.containsAll(exceptions)) {
            return Set.of();
        }
        return thrown.addAllDiff(exceptions);
    }

    /**
     * Adds the exceptions to those that {@code stmt} may throw.
     *
     * @return the exceptions that are new to {@code stmt}; a shared empty
     * set when none is new
     */
    Set<CSObj> propagate(Stmt stmt, Set<CSObj> exceptions) {
        SetEx<CSObj> thrown = explicitExceptions.get(stmt);
        if (thrown == null) {
            thrown = setFactory.get();
            explicitExceptions.put(stmt, thrown);
        } else if (thrown.containsAll(exceptions)) {
            return Set.of();
        }
        return thrown.addAllDiff(exceptions);
    }

    /**
     * @return whether {@code callSite} already may throw all
     * {@code exceptions} (its set from {@link #propagate(CSCallSite, Set)});
     * changes no element (a sparse set may drop all-zero blocks), so
     * threads may call it while nothing adds to that set.
     */
    static boolean throwsAll(CSCallSite callSite, Set<CSObj> exceptions) {
        SetEx<CSObj> thrown = callSite.getThrownExceptions();
        return thrown != null && thrown.containsAll(exceptions);
    }

    /**
     * Adds the exceptions to those that the method does not catch.
     *
     * @return the exceptions that are new to the uncaught set; a shared
     * empty set when none is new
     */
    Set<CSObj> addUncaughtExceptions(Set<CSObj> exceptions) {
        if (uncaughtExceptions.containsAll(exceptions)) {
            return Set.of();
        }
        return uncaughtExceptions.addAllDiff(exceptions);
    }

    Set<CSObj> mayThrowExplicitly(Stmt stmt) {
        Set<CSObj> result = explicitExceptions.get(stmt);
        return result != null ? result : Set.of();
    }

    Set<CSObj> mayThrowUncaught() {
        return Collections.unmodifiableSet(uncaughtExceptions);
    }

    /**
     * @return the live set of uncaught exceptions, so that a set of the same
     * factory takes it word by word; the caller must neither change it nor
     * keep it past the work that reads it
     */
    SetEx<CSObj> uncaughtSet() {
        return uncaughtExceptions;
    }
}
