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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.HeapOwnerCensus;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetCensus;
import pascal.taie.util.Indexer;

import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.HOLDERS_MANY;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.OBJECTS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.SETS;
import static pascal.taie.analysis.pta.pts.HeapOwnerCensus.UNSHARED;

public class LiveCensusTest {

    private static final String CLASS_PATH = "src/test/resources/pta/lambda";

    private static final String MAIN = "LambdaContexts";

    private static final String OPTIONS =
            "implicit-entries:false;cs:1-obj;share-points-to-sets:true;";

    @Test
    void intervalCountsFromTheEndOfTheLastCensus() {
        LiveCensusClock clock = new LiveCensusClock(10, null, 0);
        assertTrue(clock.isOn());
        assertNull(clock.due(9));
        assertEquals("interval", clock.due(10));
        clock.taken(12);
        assertNull(clock.due(21));
        assertEquals("interval", clock.due(22));
    }

    @Test
    void offWithoutIntervalAndTrigger() {
        LiveCensusClock clock = new LiveCensusClock(0, null, 0);
        assertFalse(clock.isOn());
        assertNull(clock.due(Long.MAX_VALUE / 2));
        assertThrows(IllegalArgumentException.class, () -> LiveCensusClock.of(-1, 0));
    }

    @Test
    void triggerFileAsksForOneCensusPerCreation(@TempDir Path dir) throws IOException {
        Path trigger = dir.resolve("census.now");
        LiveCensusClock clock = new LiveCensusClock(0, trigger, 0);
        assertTrue(clock.isOn());
        assertNull(clock.due(0));
        Files.createFile(trigger);
        // looked for at most once per check period
        assertNull(clock.due(LiveCensusClock.TRIGGER_CHECK_NANOS - 1));
        assertEquals("trigger", clock.due(LiveCensusClock.TRIGGER_CHECK_NANOS));
        assertFalse(Files.exists(trigger), "the trigger file was not deleted");
        assertNull(clock.due(2 * LiveCensusClock.TRIGGER_CHECK_NANOS));
    }

    /**
     * A census taken between two polls agrees with itself (the owner rows
     * of the pointers split exactly the distinct sets and objects of the
     * block census), sees no more than the census at the finish, and
     * changes neither the call graph nor any points-to set or the order of
     * the pointers and objects.
     */
    @Test
    void censusDuringTheSolveIsConsistentAndChangesNoResult(@TempDir Path dir)
            throws IOException {
        run("census:true;" + OPTIONS);
        assertEquals(0, Probe.liveCensuses);
        List<Long> pointers = Probe.pointers;
        List<Long> edges = Probe.edges;
        SolverCensus finish = Probe.census;
        HeapOwnerCensus finishOwners = Probe.owners;
        assertNotNull(finish);
        assertNotNull(finishOwners);
        assertOwnersSplitTheCensus(finish.pts(), finishOwners);
        assertTrue(finishOwners.get(HeapOwnerCensus.HOLDERS_1, SETS) > 0
                        && finishOwners.get(HeapOwnerCensus.HOLDERS_MANY, SETS) > 0,
                "shared sets are not split by holders: " + finishOwners);
        long iterations = Probe.iterations;

        Path trigger = dir.resolve("census.now");
        Files.createFile(trigger);
        System.setProperty(LiveCensusClock.TRIGGER_PROPERTY, trigger.toString());
        try {
            run("census:true;" + OPTIONS);
        } finally {
            System.clearProperty(LiveCensusClock.TRIGGER_PROPERTY);
        }
        assertEquals(1, Probe.liveCensuses);
        assertFalse(Files.exists(trigger), "the trigger file was not deleted");
        SolverCensus live = Probe.lastLiveCensus;
        HeapOwnerCensus liveOwners = Probe.lastLiveOwners;
        assertNotNull(live);
        assertNotNull(liveOwners);
        assertOwnersSplitTheCensus(live.pts(), liveOwners);
        assertTrue(live.pts().all().sets() < finish.pts().all().sets(),
                "the census was not taken during the solve: " + live.pts());
        assertTrue(live.pts().all().objects() <= finish.pts().all().objects());
        // the finish census of a run with a census during the solve is
        // that of a run without
        assertEquals(finish.pts().toString(), Probe.census.pts().toString());
        assertEquals(finishOwners.toString(), Probe.owners.toString());
        assertEquals(edges, Probe.edges);
        assertEquals(pointers, Probe.pointers);
        assertEquals(iterations, Probe.iterations);
    }

    @Test
    void censusIntervalOptionIsOffByDefault() {
        run(OPTIONS);
        assertEquals(0, Probe.liveCensuses);
        assertNull(Probe.lastLiveCensus);
        assertNull(Probe.owners);
    }

    private static void assertOwnersSplitTheCensus(PointsToSetCensus pts,
                                                   HeapOwnerCensus owners) {
        assertEquals(pts.distinct().sets(), owners.sum(UNSHARED, HOLDERS_MANY + 1, SETS),
                owners.toString());
        assertEquals(pts.distinct().objects(), owners.sum(UNSHARED, HOLDERS_MANY + 1, OBJECTS),
                owners.toString());
    }

    private static void run(String options) {
        Probe.census = null;
        Probe.owners = null;
        Main.main("-cp", CLASS_PATH, "-m", MAIN,
                "-a", "pta=" + options + "plugins:[" + Probe.class.getName() + "];");
    }

    /**
     * Checks the work list between every 64 polls, and reads at onFinish
     * the censuses, every pointer (in index order, with its objects in
     * iteration order) and the call edges.
     */
    public static class Probe implements Plugin {

        private static final long CHECK_MASK = 63;

        static SolverCensus census;

        static HeapOwnerCensus owners;

        static long liveCensuses;

        static long iterations;

        static SolverCensus lastLiveCensus;

        static HeapOwnerCensus lastLiveOwners;

        static List<Long> pointers = List.of();

        static List<Long> edges = List.of();

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
            ((DefaultSolver) solver).setProgressCheckForTesting(CHECK_MASK, 0);
        }

        @Override
        public void onFinish() {
            DefaultSolver s = (DefaultSolver) solver;
            census = (SolverCensus) field(s, "census");
            owners = (HeapOwnerCensus) field(s, "owners");
            liveCensuses = (Long) field(s, "liveCensuses");
            iterations = (Long) field(s, "iterations");
            lastLiveCensus = (SolverCensus) field(s, "lastLiveCensus");
            lastLiveOwners = (HeapOwnerCensus) field(s, "lastLiveOwners");
            Indexer<CSObj> objects = solver.getCSManager().getObjectIndexer();
            List<Long> ps = new ArrayList<>();
            solver.getCSManager().pointers()
                    .sorted(Comparator.comparingInt(Pointer::getIndex))
                    .forEach(p -> {
                        long[] h = {31L * p.getIndex() + p.getClass().getName().hashCode()};
                        PointsToSet pts = p.getPointsToSet();
                        if (pts != null) {
                            pts.forEach(o -> h[0] = 31 * h[0] + objects.getIndex(o));
                        }
                        ps.add(h[0]);
                    });
            pointers = ps;
            edges = solver.getCallGraph().edges()
                    .map(e -> (long) e.toString().hashCode()).sorted().toList();
        }

        private static Object field(DefaultSolver s, String name) {
            try {
                Field field = DefaultSolver.class.getDeclaredField(name);
                field.setAccessible(true);
                return field.get(s);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }
}
