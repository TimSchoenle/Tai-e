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
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.util.collection.GenericBitSet;
import pascal.taie.util.collection.IBitSet;
import pascal.taie.util.collection.SetEx;

import java.lang.reflect.Field;
import java.util.List;
import java.util.function.Supplier;

/**
 * Test access to the exception-set factory of the {@link ExceptionAnalysis}
 * a solver runs, and to the width of a bit set. Call it from a plugin's
 * {@code onStart}, when the solver holds its plugins.
 */
final class ExceptionAnalysisAccess {

    private ExceptionAnalysisAccess() {
    }

    @SuppressWarnings("unchecked")
    static Supplier<SetEx<CSObj>> setFactory(Solver solver) {
        try {
            return (Supplier<SetEx<CSObj>>) setFactoryField().get(exceptionAnalysis(solver));
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }

    static void replaceSetFactory(Solver solver, Supplier<SetEx<CSObj>> factory) {
        try {
            setFactoryField().set(exceptionAnalysis(solver), factory);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }

    /**
     * @return the number of 64-bit words the given bit set holds.
     */
    static int words(SetEx<CSObj> set) {
        try {
            Field bitSet = GenericBitSet.class.getDeclaredField("bitSet");
            bitSet.setAccessible(true);
            return ((IBitSet) bitSet.get(set)).size() / Long.SIZE;
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }

    private static Field setFactoryField() throws NoSuchFieldException {
        Field field = ExceptionAnalysis.class.getDeclaredField("setFactory");
        field.setAccessible(true);
        return field;
    }

    @SuppressWarnings("unchecked")
    private static ExceptionAnalysis exceptionAnalysis(Solver solver)
            throws ReflectiveOperationException {
        Field pluginField = solver.getClass().getDeclaredField("plugin");
        pluginField.setAccessible(true);
        Object composite = pluginField.get(solver);
        Field allPlugins = composite.getClass().getDeclaredField("allPlugins");
        allPlugins.setAccessible(true);
        for (Plugin plugin : (List<Plugin>) allPlugins.get(composite)) {
            if (plugin instanceof ExceptionAnalysis exceptionAnalysis) {
                return exceptionAnalysis;
            }
        }
        throw new AssertionError("the solver runs no ExceptionAnalysis");
    }
}
