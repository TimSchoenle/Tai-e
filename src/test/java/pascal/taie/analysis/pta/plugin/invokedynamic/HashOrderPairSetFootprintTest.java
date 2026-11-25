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
import pascal.taie.util.collection.HybridHashSet;

import java.lang.ref.Reference;
import java.util.Set;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Heap bytes per element of {@link HashOrderPairSet} against a
 * {@link HybridHashSet} of invocation objects of the former layout (three
 * references and two ints), at the sizes the lambda receiver variables have
 * (hundreds of invocations) and at one invocation.
 */
class HashOrderPairSetFootprintTest {

    private static final Object[] FIRSTS = new Object[500];

    private static final Object SECOND = new Object();

    static {
        for (int i = 0; i < FIRSTS.length; ++i) {
            FIRSTS[i] = new Object();
        }
    }

    @Test
    void fiveHundredPairsTakeUnderTwoFifthsOfTheHybridSet() {
        double pairs = bytesPerElement(2_000, 500, HashOrderPairSetFootprintTest::pairSet);
        double objects = bytesPerElement(2_000, 500, HashOrderPairSetFootprintTest::objectSet);
        System.out.println("[lic] bytes per invocation (500 per variable): pair set "
                + pairs + ", hybrid set of objects " + objects);
        assertTrue(pairs * 5 < objects * 2, pairs + " vs " + objects);
    }

    @Test
    void onePairTakesNoMoreThanTheHybridSet() {
        double pairs = bytesPerElement(200_000, 1, HashOrderPairSetFootprintTest::pairSet);
        double objects = bytesPerElement(200_000, 1, HashOrderPairSetFootprintTest::objectSet);
        System.out.println("[lic] bytes per invocation (1 per variable): pair set "
                + pairs + ", hybrid set of objects " + objects);
        // both 56 bytes: a 32-byte set and an Object[2], against a 24-byte
        // hybrid set and a 32-byte invocation; 4 bytes absorb GC noise
        assertTrue(pairs <= objects + 4, pairs + " vs " + objects);
    }

    private static double bytesPerElement(int sets, int elements, IntFunction<Object> filled) {
        long before = usedAfterGc();
        Object[] held = new Object[sets];
        long array = usedAfterGc() - before;
        for (int i = 0; i < sets; ++i) {
            held[i] = filled.apply(elements);
        }
        long used = usedAfterGc() - before - array;
        Reference.reachabilityFence(held);
        return (double) used / ((long) sets * elements);
    }

    private static long usedAfterGc() {
        Runtime runtime = Runtime.getRuntime();
        for (int i = 0; i < 3; ++i) {
            System.gc();
        }
        return runtime.totalMemory() - runtime.freeMemory();
    }

    private static final class Pairs extends HashOrderPairSet<Object, Object> {

        @Override
        protected int hash(Object a, Object b) {
            return 31 * a.hashCode() + b.hashCode();
        }
    }

    private static Object pairSet(int elements) {
        Pairs set = new Pairs();
        for (int i = 0; i < elements; ++i) {
            set.add(FIRSTS[i], SECOND);
        }
        return set;
    }

    /**
     * The former invocation object: call site, source and target references,
     * and the two argument counts.
     */
    private record Invocation(Object csCallSite, Object source, Object targetRef,
                              int argsToStatic, int argsToInstance) {
    }

    private static Object objectSet(int elements) {
        Set<Invocation> set = new HybridHashSet<>();
        for (int i = 0; i < elements; ++i) {
            set.add(new Invocation(FIRSTS[i], SECOND, SECOND, 1, 0));
        }
        return set;
    }
}
