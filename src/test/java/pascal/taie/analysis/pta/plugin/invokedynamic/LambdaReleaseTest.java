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
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.util.collection.MultiMap;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * With {@code release-solver-state}, {@link LambdaAnalysis#onRelease}
 * drops its solve-only caches; the points-to sets and the call graph of the
 * result stay the same as without the release, also in verify mode, whose
 * finish check runs before the caches are dropped.
 */
class LambdaReleaseTest {

    private static final String OPTIONS = "cs:1-obj;implicit-entries:false;only-app:true;"
            + "handle-invokedynamic:true;plugins:[" + Probe.class.getName() + "];";

    private static final String RELEASE = "release-solver-state:true;";

    @Test
    void releaseDropsCachesAndKeepsResult() throws Exception {
        run("");
        List<String> kept = resultLines();
        LambdaAnalysis lambda = lambdaAnalysis();
        assertFalse(multiMap(lambda, "invoInfos").isEmpty(),
                "the program has no lambda instance invocation");
        assertFalse(multiMap(lambda, "lambdaObjs").isEmpty());

        run(RELEASE);
        assertEquals(kept, resultLines());
        lambda = lambdaAnalysis();
        assertTrue(multiMap(lambda, "invoInfos").isEmpty());
        assertTrue(multiMap(lambda, "lambdaObjs").isEmpty());
        assertTrue(((Map<?, ?>) field(lambda, "recvByType")).isEmpty());
    }

    /**
     * The finish check runs once and still sees the receiver groupings
     * (its {@code cachedVars} count is read from them), so it ran before
     * they were dropped.
     */
    @Test
    void verifyModeChecksOnceBeforeTheRelease() throws Exception {
        System.setProperty("spd.lambda.verify", "true");
        PrintStream out = System.out;
        try {
            run("");
            List<String> kept = resultLines();
            ByteArrayOutputStream captured = new ByteArrayOutputStream();
            System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
            try {
                run(RELEASE);
            } finally {
                System.setOut(out);
            }
            assertEquals(kept, resultLines());
            assertTrue(multiMap(lambdaAnalysis(), "invoInfos").isEmpty());
            List<String> finishLines = captured.toString(StandardCharsets.UTF_8).lines()
                    .filter(line -> line.contains("[spd] lambda verify finish OK"))
                    .toList();
            assertEquals(1, finishLines.size(), finishLines.toString());
            assertTrue(finishLines.get(0).contains("cachedVars="), finishLines.get(0));
            assertFalse(finishLines.get(0).contains("cachedVars=0 "), finishLines.get(0));
        } finally {
            System.clearProperty("spd.lambda.verify");
        }
    }

    private static void run(String extraOptions) {
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", "LambdaContexts",
                "-a", "pta=" + extraOptions + OPTIONS);
    }

    private static List<String> resultLines() {
        PointerAnalysisResult result = World.get().getResult(PointerAnalysis.ID);
        List<String> lines = new ArrayList<>();
        result.getCSVars().forEach(v -> lines.add(v + " -> "
                + v.getObjects().stream().map(Object::toString).sorted().toList()));
        result.getCSCallGraph().edges().forEach(e -> lines.add(e.toString()));
        lines.sort(null);
        return lines;
    }

    private static LambdaAnalysis lambdaAnalysis() throws ReflectiveOperationException {
        Object composite = field(Probe.solver, "plugin");
        for (Object plugin : (List<?>) field(composite, "allPlugins")) {
            if (plugin instanceof LambdaAnalysis lambda) {
                return lambda;
            }
        }
        throw new AssertionError("no LambdaAnalysis");
    }

    private static MultiMap<?, ?> multiMap(LambdaAnalysis lambda, String name)
            throws ReflectiveOperationException {
        return (MultiMap<?, ?>) field(lambda, name);
    }

    private static Object field(Object owner, String name) throws ReflectiveOperationException {
        Class<?> c = owner.getClass();
        while (c != null) {
            try {
                Field f = c.getDeclaredField(name);
                f.setAccessible(true);
                return f.get(owner);
            } catch (NoSuchFieldException e) {
                c = c.getSuperclass();
            }
        }
        throw new NoSuchFieldException(name);
    }

    /**
     * Keeps the solver of the last run.
     */
    public static class Probe implements Plugin {

        static DefaultSolver solver;

        @Override
        public void setSolver(Solver solver) {
            Probe.solver = (DefaultSolver) solver;
        }
    }
}
