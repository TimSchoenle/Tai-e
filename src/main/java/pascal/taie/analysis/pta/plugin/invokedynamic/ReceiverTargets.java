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

import org.jspecify.annotations.Nullable;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Maps;

import java.util.Arrays;
import java.util.Map;

/**
 * The target method references of the lambda invocations on one receiver
 * variable, indexed by their declaring class, so that a receiver type finds
 * the targets it may dispatch by walking its own supertypes instead of
 * trying every target. A receiver type can dispatch a target only if the
 * target's declaring class is the type's class or one of its supertypes
 * (see {@link pascal.taie.language.classes.ClassHierarchy#dispatch}).
 * <p>
 * Per target it keeps two ascending lists of slots of a
 * {@link ReceiverGroups} keyed by receiver type: the known slots, of the
 * variable's grouping of its whole points-to set, and the delta slots, of
 * the grouping of the new points-to set being handled (event). Each list
 * holds at least the slots whose type dispatches the target.
 */
final class ReceiverTargets {

    private final Map<MethodRef, Target> byRef = Maps.newMap();

    private final Map<JClass, Target[]> byDeclaringClass = Maps.newMap();

    /**
     * @return the target of {@code ref}, or null if no invocation on the
     * variable has it yet.
     */
    @Nullable
    Target get(MethodRef ref) {
        return byRef.get(ref);
    }

    /**
     * Adds the target {@code ref}, absent so far, with no slots.
     */
    Target add(MethodRef ref) {
        Target target = new Target(ref);
        if (byRef.putIfAbsent(ref, target) != null) {
            throw new IllegalStateException("target added twice: " + ref);
        }
        byDeclaringClass.merge(ref.getDeclaringClass(), new Target[]{target},
                ReceiverTargets::concat);
        return target;
    }

    /**
     * @return the targets declared in {@code declaringClass}, or null if
     * there is none.
     */
    Target @Nullable [] declaredIn(JClass declaringClass) {
        return byDeclaringClass.get(declaringClass);
    }

    private static Target[] concat(Target[] old, Target[] added) {
        Target[] all = Arrays.copyOf(old, old.length + added.length);
        System.arraycopy(added, 0, all, old.length, added.length);
        return all;
    }

    /**
     * One target method reference of the variable and its slots.
     */
    static final class Target {

        private final MethodRef ref;

        private final SlotList known = new SlotList();

        private final SlotList delta = new SlotList();

        /**
         * The event {@link #delta} belongs to; the list is empty for any
         * other event.
         */
        private long deltaEvent = -1;

        private Target(MethodRef ref) {
            this.ref = ref;
        }

        MethodRef ref() {
            return ref;
        }

        SlotList known() {
            return known;
        }

        /**
         * Adds {@code slot} to the delta slots of {@code event}, dropping
         * those of an earlier event first.
         */
        void addDelta(long event, int slot) {
            if (deltaEvent != event) {
                deltaEvent = event;
                delta.clear();
            }
            delta.addLast(slot);
        }

        int[] deltaSlots() {
            return delta.slots;
        }

        /**
         * @return the number of delta slots of {@code event}.
         */
        int deltaCount(long event) {
            return deltaEvent == event ? delta.count : 0;
        }
    }

    /**
     * An ascending list of distinct slots.
     */
    static final class SlotList {

        private static final int[] EMPTY = {};

        private int[] slots = EMPTY;

        private int count;

        /**
         * Appends {@code slot} unless it is the last slot already.
         *
         * @throws IllegalStateException if {@code slot} is below the last
         *                               slot
         */
        void addLast(int slot) {
            if (count > 0) {
                int last = slots[count - 1];
                if (last == slot) {
                    return;
                }
                if (last > slot) {
                    throw new IllegalStateException("slot " + slot + " after " + last);
                }
            }
            if (count == slots.length) {
                // the growth of java.util.ArrayList, from capacity one
                slots = Arrays.copyOf(slots, count + Math.max(1, count >> 1));
            }
            slots[count++] = slot;
        }

        int[] slots() {
            return slots;
        }

        int count() {
            return count;
        }

        private void clear() {
            count = 0;
        }
    }
}
