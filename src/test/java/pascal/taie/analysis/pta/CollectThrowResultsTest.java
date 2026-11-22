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

package pascal.taie.analysis.pta;

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.plugin.exception.ExceptionAnalysis;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Option {@code collect-throw-results} decides whether the exception
 * analysis stores its per-method throw results after the solve; the call
 * graph is the same either way.
 */
public class CollectThrowResultsTest {

    @Test
    void storesThrowResultsByDefault() {
        run(true);
        assertNotNull(result().getResult(ExceptionAnalysis.class.getName()));
    }

    @Test
    void skipsThrowResultsWhenOffAndKeepsTheCallGraph() {
        run(true);
        Set<String> withResults = callEdges();
        run(false);
        assertNull(result().getResult(ExceptionAnalysis.class.getName()));
        assertEquals(withResults, callEdges());
    }

    @Test
    void pointerBasedThrowAnalysisRefusesMissingResults() {
        Throwable thrown = assertThrows(RuntimeException.class, () -> Main.main(
                "-cp", "src/test/resources/pta/exception",
                "-m", "ExceptionNoneCaught",
                "-a", "pta=collect-throw-results:false;",
                "-a", "throw=algorithm:pta"));
        while (thrown != null && !(thrown instanceof IllegalStateException
                && String.valueOf(thrown.getMessage()).contains("collect-throw-results"))) {
            thrown = thrown.getCause();
        }
        assertNotNull(thrown, "no failure naming collect-throw-results");
    }

    private static void run(boolean collect) {
        Main.main("-cp", "src/test/resources/pta/exception",
                "-m", "ExceptionNoneCaught",
                "-a", "pta=collect-throw-results:" + collect + ";");
    }

    private static PointerAnalysisResult result() {
        return World.get().getResult(PointerAnalysis.ID);
    }

    private static Set<String> callEdges() {
        return result().getCallGraph().edges()
                .map(e -> e.getCallSite().getContainer().getSignature()
                        + " -> " + e.getCallee().getSignature())
                .collect(Collectors.toSet());
    }
}
