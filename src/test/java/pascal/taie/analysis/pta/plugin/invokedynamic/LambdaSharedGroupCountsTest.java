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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.CompositePlugin;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.lang.reflect.Field;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The paths of {@link ReceiverGroupCache#advance} that the equivalence test
 * (LambdaSharedReceiverGroupsTest) relies on run on its fixtures: variables
 * join a grouping another variable built, and copy a grouping still held by
 * others, as the counts of the lambda analysis' grouping table read.
 */
class LambdaSharedGroupCountsTest {

    private static final Pattern COUNTS = Pattern.compile(
            "sharedGroupings=\\d+ extensions=(\\d+) joins=(\\d+) copies=(\\d+) rebuilds=(\\d+)");

    /**
     * @return the counts line of the grouping table after solving
     * {@code main} of the lambda fixtures under {@code cs}
     */
    private static String counts(String main, String cs) {
        Probe.line = null;
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", main,
                "-a", "pta=implicit-entries:false;cs:" + cs
                        + ";handle-invokedynamic:true;share-points-to-sets:true"
                        + ";lambda-shared-receiver-groups:true;plugins:["
                        + Probe.class.getName() + "];");
        assertNotNull(Probe.line, "no lambda analysis in " + main);
        return Probe.line;
    }

    /**
     * LambdaSharedReceiver and Streams, both in the equivalence test, join
     * and copy groupings without a rebuild; Streams also extends one in
     * place.
     */
    @ParameterizedTest
    @CsvSource({"LambdaSharedReceiver, 1-obj, false", "LambdaSharedReceiver, ci, false",
            "Streams, 1-obj, true", "Streams, ci, true"})
    void joinsAndCopiesHappenOnTheFixture(String main, String cs, boolean extended) {
        String line = counts(main, cs);
        Matcher m = COUNTS.matcher(line);
        assertTrue(m.matches(), line);
        assertTrue(Long.parseLong(m.group(2)) > 0, "no join: " + line);
        assertTrue(Long.parseLong(m.group(3)) > 0, "no copy: " + line);
        assertEquals(0, Long.parseLong(m.group(4)), "rebuilds: " + line);
        if (extended) {
            assertTrue(Long.parseLong(m.group(1)) > 0, "no extension: " + line);
        }
    }

    /**
     * Reads at onFinish (after the lambda analysis' own onFinish) the counts
     * of the solver's lambda analysis' grouping table.
     */
    public static class Probe implements Plugin {

        static String line;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            Object composite = field(DefaultSolver.class, solver, "plugin");
            @SuppressWarnings("unchecked")
            List<Plugin> plugins = (List<Plugin>) field(CompositePlugin.class, composite,
                    "allPlugins");
            for (Plugin p : plugins) {
                if (p instanceof LambdaAnalysis lambda) {
                    line = ((ReceiverGroupCache<?, ?>) field(LambdaAnalysis.class, lambda,
                            "receiverGroups")).countsLine();
                }
            }
        }

        private static Object field(Class<?> owner, Object target, String name) {
            try {
                Field field = owner.getDeclaredField(name);
                field.setAccessible(true);
                return field.get(target);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
