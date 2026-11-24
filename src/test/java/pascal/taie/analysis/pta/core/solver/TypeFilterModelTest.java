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
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.Sets;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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

    private static int objectTypeCount;

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
            objectTypeCount = guards.size();
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
            probeThrowingCheck(types, objects.get(0));
            probeChecksPerType(types, objects);
            probeTypeIdsBeyondFirstWord(types, objects, true);
            probeTypeIdsBeyondFirstWord(types, objects, false);
            probeNoObjectLookupForKnownTypes(types, objects);
        }

        /**
         * Gives the types of the objects their ids in two steps, one object
         * per type each: first 64 types (ids 0 to 63, one word of a type
         * memo), then the other types (ids of 64 and above). The other
         * objects of the late types are then filtered with no type check:
         * their answers come from the type memo beyond its first word, for
         * a passing and a failing type alike. Either in bit sets or each
         * object alone (the object-by-object path).
         */
        private void probeTypeIdsBeyondFirstWord(TypeSystem types, List<CSObj> objects,
                                                 boolean bitSets) {
            String path = bitSets ? "bit set path" : "object-by-object path";
            Type guard = types.getArrayType(types.getClassType("java.lang.Object"), 3);
            Map<Type, List<CSObj>> byType = new LinkedHashMap<>();
            objects.forEach(o -> byType.computeIfAbsent(o.getObject().getType(),
                    t -> new ArrayList<>()).add(o));
            Type passing = null;
            Type failing = null;
            for (Map.Entry<Type, List<CSObj>> e : byType.entrySet()) {
                if (e.getValue().size() < 2) {
                    continue;
                }
                if (types.isAssignable(guard, e.getKey())) {
                    passing = passing == null ? e.getKey() : passing;
                } else {
                    failing = failing == null ? e.getKey() : failing;
                }
            }
            if (passing == null || failing == null || byType.size() < Long.SIZE + 2) {
                FAILURES.add(path + ": no passing and failing type with two objects among "
                        + byType.size() + " types");
                return;
            }
            List<Type> order = new ArrayList<>(byType.keySet());
            order.remove(passing);
            order.remove(failing);
            order.add(passing);
            order.add(failing);
            List<Type> early = order.subList(0, Long.SIZE);
            List<Type> late = order.subList(Long.SIZE, order.size());
            int[] checks = {0};
            Solver counting = countingChecks(types, checks);
            TypeFilter.clearMemos();
            List<CSObj> firstEarly = new ArrayList<>();
            early.forEach(t -> firstEarly.add(byType.get(t).get(0)));
            List<CSObj> firstLate = new ArrayList<>();
            List<CSObj> otherLate = new ArrayList<>();
            for (Type t : late) {
                List<CSObj> objs = byType.get(t);
                firstLate.add(objs.get(0));
                otherLate.addAll(objs.subList(1, objs.size()));
            }
            filterAll(guard, counting, firstEarly, bitSets);
            filterAll(guard, counting, firstLate, bitSets);
            if (checks[0] != order.size()) {
                FAILURES.add(path + ": " + checks[0] + " checks for the first objects of "
                        + order.size() + " types");
            }
            checks[0] = 0;
            List<CSObj> got = filterAll(guard, counting, otherLate, bitSets);
            if (checks[0] != 0) {
                FAILURES.add(path + ": " + checks[0]
                        + " checks for objects of types with ids of 64 and above");
            }
            List<CSObj> want = otherLate.stream()
                    .filter(o -> types.isAssignable(guard, o.getObject().getType()))
                    .toList();
            if (!Set.copyOf(want).equals(Set.copyOf(got)) || want.size() != got.size()) {
                FAILURES.add(path + ": late types filtered to " + got + ", expected " + want);
            }
            Type pass = passing;
            Type fail = failing;
            if (got.stream().noneMatch(o -> o.getObject().getType().equals(pass))
                    || got.stream().anyMatch(o -> o.getObject().getType().equals(fail))) {
                FAILURES.add(path + ": late passing type " + pass + " or failing type "
                        + fail + " read wrongly from the type memo: " + got);
            }
        }

        /**
         * Filters the objects with a new filter of the guard, all in one
         * points-to set or each object alone.
         *
         * @return the objects that passed
         */
        private List<CSObj> filterAll(Type guard, Solver s, List<CSObj> objs, boolean bitSets) {
            List<CSObj> passed = new ArrayList<>();
            if (bitSets) {
                PointsToSet pts = solver.makePointsToSet();
                objs.forEach(pts::addObject);
                if (TypeFilter.representation(pts) != 2) {
                    FAILURES.add("a set of " + objs.size() + " objects is not a bit set");
                }
                passed.addAll(new TypeFilter(guard, s).apply(null, pts).getObjects());
            } else {
                for (CSObj o : objs) {
                    PointsToSet one = solver.makePointsToSet();
                    one.addObject(o);
                    passed.addAll(new TypeFilter(guard, s).apply(null, one).getObjects());
                }
            }
            return passed;
        }

        /**
         * Filters all objects in one bit set with a new guard type after
         * another guard gave every object its type id: the bit-set path
         * then reads no object from the object indexer to check it (only
         * the objects of a result too small for a bit set are read, to
         * collect them).
         */
        private void probeNoObjectLookupForKnownTypes(TypeSystem types, List<CSObj> objects) {
            Indexer<CSObj> real = solver.getCSManager().getObjectIndexer();
            int[] lookups = {0};
            Indexer<CSObj> counting = new Indexer<>() {
                @Override
                public int getIndex(CSObj o) {
                    return real.getIndex(o);
                }

                @Override
                public CSObj getObject(int index) {
                    lookups[0]++;
                    return real.getObject(index);
                }
            };
            PointsToSetFactory factory = new PointsToSetFactory(counting);
            CSManager csManager = (CSManager) Proxy.newProxyInstance(
                    CSManager.class.getClassLoader(), new Class<?>[]{CSManager.class},
                    (proxy, method, args) -> method.getName().equals("getObjectIndexer")
                            ? counting : invoke(method, solver.getCSManager(), args));
            Solver countingSolver = (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> switch (method.getName()) {
                        case "getCSManager" -> csManager;
                        case "makePointsToSet" -> factory.make();
                        default -> invoke(method, solver, args);
                    });
            PointsToSet all = factory.make();
            objects.forEach(all::addObject);
            if (TypeFilter.representation(all) != 2) {
                FAILURES.add("the objects of the lookup probe are not held in a bit set");
            }
            TypeFilter.clearMemos();
            new TypeFilter(types.getClassType("java.lang.Object"), countingSolver)
                    .apply(null, all);
            lookups[0] = 0;
            PointsToSet result = new TypeFilter(types.getClassType("A"), countingSolver)
                    .apply(null, all);
            int collected = TypeFilter.representation(result) == 2 ? 0 : result.size();
            if (lookups[0] != collected) {
                FAILURES.add("bit set path with known type ids: " + lookups[0]
                        + " object lookups for " + objects.size() + " objects, "
                        + result.size() + " passing");
            }
            TypeFilter.clearMemos();
        }

        private Solver countingChecks(TypeSystem types, int[] checks) {
            TypeSystem counting = (TypeSystem) Proxy.newProxyInstance(
                    TypeSystem.class.getClassLoader(), new Class<?>[]{TypeSystem.class},
                    (proxy, method, args) -> {
                        if (method.getName().equals("isAssignable")) {
                            checks[0]++;
                        }
                        return invoke(method, types, args);
                    });
            return (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> method.getName().equals("getTypeSystem")
                            ? counting : invoke(method, solver, args));
        }

        /**
         * Filters every object with a type system that counts its checks,
         * once all objects in one bit set and once each object alone (the
         * object-by-object path): objects of one type share the answer, so
         * each path asks the type system once per distinct object type.
         */
        private void probeChecksPerType(TypeSystem types, List<CSObj> objects) {
            Set<Type> objectTypes = Sets.newLinkedSet();
            objects.forEach(o -> objectTypes.add(o.getObject().getType()));
            if (objectTypes.size() >= objects.size()) {
                FAILURES.add("no two objects share a type");
            }
            int[] checks = {0};
            TypeSystem counting = (TypeSystem) Proxy.newProxyInstance(
                    TypeSystem.class.getClassLoader(), new Class<?>[]{TypeSystem.class},
                    (proxy, method, args) -> {
                        if (method.getName().equals("isAssignable")) {
                            checks[0]++;
                        }
                        return invoke(method, types, args);
                    });
            Solver countingSolver = (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> method.getName().equals("getTypeSystem")
                            ? counting : invoke(method, solver, args));
            PointsToSet all = solver.makePointsToSet();
            objects.forEach(all::addObject);
            if (TypeFilter.representation(all) != 2) {
                FAILURES.add("all objects are not held in a bit set");
            }
            // every object type passes java.lang.Object; some fail A
            for (String name : List.of("java.lang.Object", "A")) {
                Type guard = types.getClassType(name);
                TypeFilter.clearMemos();
                checks[0] = 0;
                new TypeFilter(guard, countingSolver).apply(null, all);
                if (checks[0] != objectTypes.size()) {
                    FAILURES.add(name + " bit set path: " + checks[0] + " checks for "
                            + objectTypes.size() + " object types");
                }
                TypeFilter.clearMemos();
                checks[0] = 0;
                for (CSObj o : objects) {
                    PointsToSet one = solver.makePointsToSet();
                    one.addObject(o);
                    new TypeFilter(guard, countingSolver).apply(null, one);
                }
                if (checks[0] != objectTypes.size()) {
                    FAILURES.add(name + " object-by-object path: " + checks[0]
                            + " checks for " + objectTypes.size() + " object types");
                }
            }
        }

        /**
         * Filters one object (the object-by-object path) with a type system
         * whose first check throws: the object must stay unchecked in the
         * memo, so the next filter checks it again and lets it pass.
         */
        private void probeThrowingCheck(TypeSystem types, CSObj obj) {
            TypeFilter.clearMemos();
            Type guard = obj.getObject().getType();
            boolean[] thrown = {false};
            TypeSystem throwingOnce = (TypeSystem) Proxy.newProxyInstance(
                    TypeSystem.class.getClassLoader(), new Class<?>[]{TypeSystem.class},
                    (proxy, method, args) -> {
                        if (method.getName().equals("isAssignable") && !thrown[0]) {
                            thrown[0] = true;
                            throw new IllegalStateException("check failed");
                        }
                        return invoke(method, types, args);
                    });
            Solver throwingSolver = (Solver) Proxy.newProxyInstance(
                    Solver.class.getClassLoader(), new Class<?>[]{Solver.class},
                    (proxy, method, args) -> method.getName().equals("getTypeSystem")
                            ? throwingOnce : invoke(method, solver, args));
            PointsToSet input = solver.makePointsToSet();
            input.addObject(obj);
            try {
                new TypeFilter(guard, throwingSolver).apply(null, input);
                FAILURES.add("the throwing check did not throw");
            } catch (IllegalStateException expected) {
                // the check failed; the object must stay unchecked
            }
            PointsToSet again = new TypeFilter(guard, solver).apply(null, input);
            if (!again.contains(obj)) {
                FAILURES.add("an object whose check threw was read as failing: " + obj);
            }
        }

        private static Object invoke(Method method, Object target, Object[] args)
                throws Throwable {
            try {
                return method.invoke(target, args);
            } catch (InvocationTargetException e) {
                throw e.getCause();
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
        // more object types than one word of a type memo holds (64 bits)
        assertTrue(objectTypeCount > Long.SIZE, "object types: " + objectTypeCount);
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
