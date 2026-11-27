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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.CompositePlugin;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.lang.reflect.Field;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lambda analysis' counters count what they name.
 */
public class LambdaCountersTest {

    private final TrieContext.Factory<String> contexts = new TrieContext.Factory<>();

    private final Context empty = contexts.getEmptyContext();

    private final Context other = contexts.make("c");

    @Test
    void countsEntersAndHitsPerPath() {
        LambdaCounters c = new LambdaCounters();
        c.enter(LambdaCounters.PATH_CALL, true);
        c.enter(LambdaCounters.PATH_CALL, false);
        c.enter(LambdaCounters.PATH_SHARED, true);
        assertEquals(2, c.enters(LambdaCounters.PATH_CALL));
        assertEquals(1, c.enterHits(LambdaCounters.PATH_CALL));
        assertEquals(0, c.enters(LambdaCounters.PATH_NEW_PTS));
        assertEquals(1, c.enterHits(LambdaCounters.PATH_SHARED));
    }

    @Test
    void countsRepeatedThisUpdatesPerEventAndCallee() {
        LambdaCounters c = new LambdaCounters();
        c.startEvent();
        c.thisUpdate(empty, null);
        c.thisUpdate(other, null);
        c.thisUpdate(empty, null);
        c.startEvent();
        c.thisUpdate(empty, null);
        assertEquals(4, c.thisUpdates());
        assertEquals(1, c.repeatedThisUpdates());
    }

    @Test
    void countsEdgesAndTheInfosHistogram() {
        LambdaCounters c = new LambdaCounters();
        c.edgeOffered();
        c.edgeOffered();
        c.edgeNew();
        assertEquals(2, c.edgesOffered());
        assertEquals(1, c.edgesNew());
        String line = c.line(List.of(1, 1, 3));
        assertTrue(line.startsWith("enter_call=0/0 enter_new_pts=0/0 enter_shared=0/0 "), line);
        assertTrue(line.contains(" edges_offered=2 edges_new=1 "), line);
        assertTrue(line.contains(" receiver_vars=3 "), line);
        assertTrue(line.endsWith(" infos_per_receiver_var={[1,1]=2, [2,3]=1}"), line);
    }

    @Test
    void countsRedundantEdgesPerPathRepeatedCallsAndRedundantThisUpdates() {
        LambdaCounters c = new LambdaCounters();
        c.edgeRedundant(LambdaCounters.PATH_CALL);
        c.edgeRedundant(LambdaCounters.PATH_SHARED);
        c.edgeRedundant(LambdaCounters.PATH_SHARED);
        c.edgeRedundant(LambdaCounters.EDGE_PATH_SINGLE);
        c.repeatedSiteSourceCall();
        c.skippedSiteSourceCall();
        c.redundantThisUpdate();
        c.redundantThisUpdate();
        assertEquals(1, c.redundantEdges(LambdaCounters.PATH_CALL));
        assertEquals(0, c.redundantEdges(LambdaCounters.PATH_NEW_PTS));
        assertEquals(2, c.redundantEdges(LambdaCounters.PATH_SHARED));
        assertEquals(1, c.redundantEdges(LambdaCounters.EDGE_PATH_SINGLE));
        assertEquals(1, c.repeatedSiteSourceCalls());
        assertEquals(1, c.skippedSiteSourceCalls());
        assertEquals(2, c.redundantThisUpdates());
        String line = c.line(List.of());
        assertTrue(line.contains(" edges_redundant_call=1 edges_redundant_new_pts=0"
                + " edges_redundant_shared=2 edges_redundant_single=1"
                + " site_source_calls_repeated=1 site_source_calls_skipped=1"
                + " this_updates_redundant=2 "), line);
    }

    /**
     * A pointer analysis that keeps counters counts in its lambda analysis.
     */
    @Test
    void lambdaAnalysisCountsWhenThePointerAnalysisKeepsCounters() {
        Probe.counters = null;
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", "LambdaContexts",
                "-a", "pta=implicit-entries:false;cs:1-obj;census:true;plugins:["
                        + Probe.class.getName() + "];");
        LambdaCounters c = Probe.counters;
        assertNotNull(c, "the lambda analysis kept no counters");
        assertTrue(c.enters(LambdaCounters.PATH_CALL) > 0, "no enter counted");
        assertTrue(c.thisUpdates() > 0, "no this update counted");
        assertTrue(c.edgesOffered() > 0 && c.edgesNew() > 0
                && c.edgesNew() <= c.edgesOffered(), "edges not counted");
    }

    /**
     * The skip option acts on the fixture LambdaContexts under 2-obj, as the
     * counters read, so the equivalence test (LambdaRepeatEquivalenceTest)
     * compares runs that differ. (The prefilter skips no edge on any fixture
     * of that test: there, every offered edge the call graph does not take
     * as new is a duplicate still on the work list, not in the call graph.)
     */
    @Test
    void skipOptionFiresOnTheFixture() {
        String on = "lambda-edge-prefilter:true;lambda-skip-repeated-call:true;";
        LambdaCounters c = solveWithCounters("LambdaContexts", "2-obj", on);
        assertTrue(c.skippedSiteSourceCalls() > 0, "the skip option skipped no call");
        LambdaCounters off = solveWithCounters("LambdaContexts", "2-obj",
                "lambda-edge-prefilter:true;lambda-skip-repeated-call:false;");
        assertEquals(0, off.skippedSiteSourceCalls(), "skips with the option off");
        assertTrue(off.repeatedSiteSourceCalls() >= c.skippedSiteSourceCalls(),
                "repeated calls counted without the option");
    }

    private static LambdaCounters solveWithCounters(String main, String cs, String options) {
        Probe.counters = null;
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", main,
                "-a", "pta=implicit-entries:false;only-app:true;handle-invokedynamic:true;"
                        + "cs:" + cs + ";census:true;" + options + "plugins:["
                        + Probe.class.getName() + "];");
        LambdaCounters c = Probe.counters;
        Probe.counters = null;
        assertNotNull(c, "the lambda analysis kept no counters");
        return c;
    }

    /**
     * Reads at onFinish (after the lambda analysis' own onFinish) the
     * counters of the solver's lambda analysis.
     */
    public static class Probe implements Plugin {

        static LambdaCounters counters;

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
                    counters = (LambdaCounters) field(LambdaAnalysis.class, lambda, "counters");
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

    @Test
    void tellsOnlyItsOwnLambdaObjects() {
        assertFalse(LambdaAnalysis.isLambdaObj(
                new MockObj(() -> "LambdaObj", "indy", null, null, true)));
    }
}
