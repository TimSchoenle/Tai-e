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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Model test of {@link TypeFilter}: on random guard types and random
 * points-to sets of every representation (empty, singleton, small set, bit
 * set, and the bit-set deltas that {@link PointsToSet#addAllDiff} makes),
 * the filter gives the same objects in the same order and representation
 * as checking the objects of the input one by one, returns a bit-set input
 * itself exactly when all its objects pass and they do not fit a small
 * set, and leaves the input unchanged. The guard types' memos fill up
 * across the trials, so inputs with unchecked, partly checked and fully
 * checked objects all occur.
 */
class TypeFilterModelTest {

    private static final long SEED = 0x7F17E5L;

    private static final int TRIALS = 4000;

    /**
     * Per representation of the input (0 to 2, see
     * {@link TypeFilter#representation}) and of the expected result.
     */
    private static final int[][] COVERAGE = new int[3][3];

    private static final List<String> FAILURES = new ArrayList<>();

    private static int objectCount;

    private static int identityResults;

    /**
     * Runs the trials on the solver's objects at the end of the analysis.
     * Public with a no-argument constructor: the analysis loads it by name.
     */
    public static class Trials implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            List<CSObj> objects = new ArrayList<>(solver.getCSManager().getObjects());
            objectCount = objects.size();
            TypeSystem types = solver.getTypeSystem();
            Set<Type> guards = Sets.newLinkedSet();
            objects.forEach(o -> guards.add(o.getObject().getType()));
            for (String name : List.of("A", "B", "C", "D", "E", "F", "G", "I", "J",
                    "java.lang.Object", "java.lang.Cloneable")) {
                Type t = types.getClassType(name);
                if (t == null) {
                    FAILURES.add("no class type " + name);
                    continue;
                }
                guards.add(t);
                guards.add(types.getArrayType(t, 1));
            }
            List<Type> guardList = new ArrayList<>(guards);
            Random random = new Random(SEED);
            for (int trial = 0; trial < TRIALS; ++trial) {
                Type guard = guardList.get(random.nextInt(guardList.size()));
                PointsToSet input = randomInput(random, objects);
                // a second application on the same input finds every
                // object of it in the memo
                int applications = random.nextBoolean() ? 1 : 2;
                for (int i = 0; i < applications; ++i) {
                    checkOne(types, guard, input, trial);
                }
            }
        }

        private void checkOne(TypeSystem types, Type guard, PointsToSet input, int trial) {
            List<CSObj> before = new ArrayList<>(input.getObjects());
            PointsToSet expected = solver.makePointsToSet();
            for (CSObj o : before) {
                if (types.isAssignable(guard, o.getObject().getType())) {
                    expected.addObject(o);
                }
            }
            PointsToSet got = new TypeFilter(guard, solver).apply(null, input);
            int inRep = TypeFilter.representation(input);
            int wantRep = TypeFilter.representation(expected);
            COVERAGE[inRep][wantRep]++;
            boolean wantIdentity = inRep == 2 && wantRep == 2
                    && expected.size() == before.size();
            if (got == input) {
                identityResults++;
            }
            List<CSObj> want = new ArrayList<>(expected.getObjects());
            List<CSObj> have = new ArrayList<>(got.getObjects());
            if (!want.equals(have)
                    || wantRep != TypeFilter.representation(got)
                    || wantIdentity != (got == input)
                    || !before.equals(new ArrayList<>(input.getObjects()))) {
                FAILURES.add("trial " + trial + " guard " + guard + ": input " + before
                        + " (" + inRep + "), expected " + want + " (" + wantRep
                        + ", identity " + wantIdentity + "), got " + have + " ("
                        + TypeFilter.representation(got) + ", identity " + (got == input) + ")");
            }
        }

        private PointsToSet randomInput(Random random, List<CSObj> objects) {
            return switch (random.nextInt(6)) {
                case 0 -> solver.makePointsToSet();
                case 1 -> setOf(random, objects, 1);
                case 2 -> setOf(random, objects, 2 + random.nextInt(7));
                case 3 -> setOf(random, objects, 9 + random.nextInt(objects.size() - 9));
                case 4 -> {
                    // a delta held in a bit set, often with few objects
                    PointsToSet base = setOf(random, objects,
                            9 + random.nextInt(objects.size() - 9));
                    PointsToSet other = setOf(random, objects,
                            9 + random.nextInt(objects.size() - 9));
                    yield base.addAllDiff(other);
                }
                default -> {
                    // all objects of a few types: many of them pass
                    Set<Type> picked = Sets.newLinkedSet();
                    for (int i = 0; i < 1 + random.nextInt(3); ++i) {
                        picked.add(objects.get(random.nextInt(objects.size()))
                                .getObject().getType());
                    }
                    PointsToSet pts = solver.makePointsToSet();
                    objects.stream()
                            .filter(o -> picked.contains(o.getObject().getType()))
                            .forEach(pts::addObject);
                    yield pts;
                }
            };
        }

        private PointsToSet setOf(Random random, List<CSObj> objects, int size) {
            List<CSObj> shuffled = new ArrayList<>(objects);
            Collections.shuffle(shuffled, random);
            PointsToSet pts = solver.makePointsToSet();
            shuffled.subList(0, size).forEach(pts::addObject);
            return pts;
        }
    }

    @BeforeAll
    static void analyze() {
        Main.main("-cp", "src/test/resources/pta/typefilter", "-m", "TypeFilterModel",
                "-a", "pta=only-app:true;implicit-entries:false;cs:2-obj;plugins:["
                        + Trials.class.getName() + "]");
    }

    @Test
    void filterAgreesWithCheckingEachObject() {
        assertEquals(List.of(), FAILURES.subList(0, Math.min(5, FAILURES.size())),
                FAILURES.size() + " of the trials differ");
    }

    @Test
    void trialsCoverEveryRepresentation() {
        // more objects than one bit-set block holds
        assertTrue(objectCount > 512, "objects: " + objectCount);
        for (int in = 0; in < 3; ++in) {
            for (int want = 0; want < 3; ++want) {
                if (in < 2 && want > in) {
                    continue; // a filter cannot grow its input
                }
                assertTrue(COVERAGE[in][want] > 0,
                        "no trial with input representation " + in
                                + " and result representation " + want);
            }
        }
        assertTrue(identityResults > 0, "no trial returned its input");
    }
}
