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

package pascal.taie.analysis.pta.pts;

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.TestElements;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The census of the points-to sets of a solve, against the census lines of
 * the version that collected the objects of a set once per holder
 * (Tai-e px.24): byte for byte, and against that algorithm run here on the
 * same sets.
 */
public class PointsToSetCensusSolveTest {

    private static final String CLASS_PATH = "src/test/resources/pta/lambda";

    private static final String MAIN = "LambdaContexts";

    private static final String OPTIONS = "implicit-entries:false;cs:1-obj;";

    /**
     * The census lines of px.24 on the fixture with shared sets.
     */
    private static final String SHARED_PX24 = "pts-census all: sets=109 objects=141 blocks=109"
            + " words=109 cardinality={[1,1]=93, [2,3]=16}"
            + " words-per-block={1=109, 2=0, 3=0, 4=0, 5=0, 6=0, 7=0, 8=0}"
            + " blocks-per-set={[1,1]=109}\n"
            + "pts-census distinct: sets=38 objects=54 blocks=38 words=38"
            + " cardinality={[1,1]=30, [2,3]=8}"
            + " words-per-block={1=38, 2=0, 3=0, 4=0, 5=0, 6=0, 7=0, 8=0}"
            + " blocks-per-set={[1,1]=38}\n"
            + "pts-census bytes (distinct, estimate): today=2896 packed=2896 large-sets=0"
            + " large-today=0 large-packed=0 large-stored-packed=0 large-stored=0";

    /**
     * The census lines of px.24 on the fixture without shared sets.
     */
    private static final String UNSHARED_PX24 = "pts-census all: sets=109 objects=141 blocks=109"
            + " words=109 cardinality={[1,1]=93, [2,3]=16}"
            + " words-per-block={1=109, 2=0, 3=0, 4=0, 5=0, 6=0, 7=0, 8=0}"
            + " blocks-per-set={[1,1]=109}\n"
            + "pts-census distinct: sets=109 objects=141 blocks=109 words=109"
            + " cardinality={[1,1]=93, [2,3]=16}"
            + " words-per-block={1=109, 2=0, 3=0, 4=0, 5=0, 6=0, 7=0, 8=0}"
            + " blocks-per-set={[1,1]=109}\n"
            + "pts-census bytes (distinct, estimate): today=7640 packed=7640 large-sets=0"
            + " large-today=0 large-packed=0 large-stored-packed=0 large-stored=0";

    private static final int SYNTHETIC_OBJECTS = 70_000;

    private static final int SYNTHETIC_SETS = 60;

    /**
     * The census lines of px.24 on the synthetic holders.
     */
    private static final String SYNTHETIC_PX24 = "pts-census all: sets=224 objects=187644"
            + " blocks=20655 words=100971 cardinality={[0,0]=45, [1,1]=2, [4,7]=3, [8,15]=4,"
            + " [16,31]=6, [32,63]=5, [64,127]=12, [128,255]=15, [256,511]=18, [512,1023]=30,"
            + " [1024,2047]=54, [2048,4095]=30} words-per-block={1=2316, 2=2204, 3=2011,"
            + " 4=2178, 5=2382, 6=2724, 7=3472, 8=3368} blocks-per-set={[0,0]=45, [1,1]=5,"
            + " [4,7]=4, [8,15]=5, [16,31]=3, [32,63]=7, [64,127]=23, [128,255]=132}\n"
            + "pts-census distinct: sets=60 objects=60654 blocks=6797 words=32933"
            + " cardinality={[0,0]=1, [1,1]=1, [4,7]=1, [8,15]=1, [16,31]=2, [32,63]=2,"
            + " [64,127]=4, [128,255]=5, [256,511]=6, [512,1023]=10, [1024,2047]=17,"
            + " [2048,4095]=10} words-per-block={1=771, 2=734, 3=681, 4=734, 5=789, 6=902,"
            + " 7=1130, 8=1056} blocks-per-set={[0,0]=1, [1,1]=2, [4,7]=1, [8,15]=1,"
            + " [16,31]=2, [32,63]=2, [64,127]=8, [128,255]=43}\n"
            + "pts-census bytes (distinct, estimate): today=586296 packed=320328"
            + " large-sets=57 large-today=586032 large-packed=320064 large-stored-packed=0"
            + " large-stored=586032";

    @Test
    void sharedSetsGiveTheLinesOfTheCensusPerHolder() {
        run("share-points-to-sets:true;");
        assertTrue(Fixture.allSets > Fixture.distinctSets,
                "no set has two holders: " + Fixture.census);
        assertEquals(Fixture.reference, Fixture.allAndDistinct);
        assertEquals(SHARED_PX24, Fixture.census);
    }

    @Test
    void unsharedSetsGiveTheLinesOfTheCensusPerHolder() {
        run("share-points-to-sets:false;");
        assertEquals(Fixture.reference, Fixture.allAndDistinct);
        assertEquals(UNSHARED_PX24, Fixture.census);
    }

    /**
     * Sets of many blocks, words and areas (small, large and empty ones),
     * each held by one to five holders in interleaved order, and holders
     * without a set.
     */
    @Test
    void repeatedSetsOfManyBlocksGiveTheLinesOfTheCensusPerHolder() {
        CSObj[] objs = TestElements.objects(SYNTHETIC_OBJECTS);
        PointsToSetFactory factory = new PointsToSetFactory(TestElements.indexer(objs));
        List<PointsToSet> distinct = new ArrayList<>();
        for (int k = 0; k < SYNTHETIC_SETS; k++) {
            PointsToSet set = factory.make();
            for (int j = 0; j < k * k; j++) {
                set.addObject(objs[(k * 37 + j * j * 13 + j * 101) % SYNTHETIC_OBJECTS]);
            }
            distinct.add(set);
        }
        List<PointsToSet> holders = new ArrayList<>();
        for (int round = 0; round < 5; round++) {
            for (int k = 0; k < SYNTHETIC_SETS; k++) {
                if (k % 5 >= round) {
                    holders.add(distinct.get(k));
                }
                if (k % 7 == round) {
                    holders.add(null);
                }
            }
        }
        PointsToSetCensus c = new PointsToSetCensus();
        holders.forEach(c::add);
        c.finish();
        assertTrue(c.all().sets() > c.distinct().sets() && c.largeDistinct() > 0
                && c.all().blocks() > c.all().sets(), "the fixture is too plain: " + c);
        assertEquals(Fixture.perHolder(holders), c.all() + "\n" + c.distinct());
        assertTrue(c.wallNanos() > 0);
        assertEquals(SYNTHETIC_PX24, c.toString());
    }

    private static void run(String options) {
        Fixture.census = null;
        Main.main("-cp", CLASS_PATH, "-m", MAIN,
                "-a", "pta=" + OPTIONS + options + "plugins:[" + Fixture.class.getName() + "];");
        assertNotNull(Fixture.census);
    }

    /**
     * Takes at onFinish the census of every pointer and mock pointer in
     * index order (as the solver's census does) and the reference figures;
     * keeps only their text and set counts.
     */
    public static class Fixture implements Plugin {

        static String census;

        static String allAndDistinct;

        static String reference;

        static long allSets;

        static long distinctSets;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            List<PointsToSet> sets = new ArrayList<>();
            Stream.concat(solver.getCSManager().pointers(),
                            solver.getCSManager().mockPointers())
                    .sorted(Comparator.comparingInt(Pointer::getIndex))
                    .forEach(p -> sets.add(p.getPointsToSet()));
            PointsToSetCensus c = new PointsToSetCensus();
            sets.forEach(c::add);
            c.finish();
            census = c.toString();
            allAndDistinct = c.all() + "\n" + c.distinct();
            allSets = c.all().sets();
            distinctSets = c.distinct().sets();
            reference = perHolder(sets);
        }

        /**
         * The populations as px.24 counted them: the objects of a set
         * collected for every holder.
         */
        private static String perHolder(List<PointsToSet> sets) {
            PointsToSetCensus.Population all = new PointsToSetCensus.Population();
            PointsToSetCensus.Population distinct = new PointsToSetCensus.Population();
            Set<PointsToSet> seen = Collections.newSetFromMap(new IdentityHashMap<>());
            for (PointsToSet pts : sets) {
                if (pts == null) {
                    all.record(new int[0], 0);
                    continue;
                }
                int[] sorted = pts.objects().mapToInt(CSObj::getIndex).toArray();
                Arrays.sort(sorted);
                all.record(sorted, sorted.length);
                if (seen.add(pts)) {
                    distinct.record(sorted, sorted.length);
                }
            }
            return all + "\n" + distinct;
        }
    }
}
