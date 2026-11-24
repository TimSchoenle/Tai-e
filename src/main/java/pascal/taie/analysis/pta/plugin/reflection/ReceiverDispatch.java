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

package pascal.taie.analysis.pta.plugin.reflection;

import org.jspecify.annotations.Nullable;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * Dispatches the reflectively invoked instance methods of one
 * {@code Method.invoke} handler call on that call's receiver objects.
 * <p>
 * At the first target the receivers are copied once, in their iteration
 * order, into an array, and each distinct receiver type gets a dense id
 * (one map probe per receiver). Every target then walks the same arrays;
 * the hierarchy is asked once per (target, receiver type), at the first
 * receiver of that type, and the answers, {@code null} included, are kept
 * in an array reused by all targets. The method reference of a target is
 * built at its first dispatch, not once per receiver. For one type and one
 * reference the answer cannot change: loading classes adds classes but
 * never changes a loaded class's supertypes or methods.
 * <p>
 * The receivers must not change during the handler call: the solver queues
 * new points-to facts instead of adding them to a set being iterated.
 *
 * @param <R> the type of the receivers
 */
final class ReceiverDispatch<R> {

    private static final Object[] NO_RECEIVERS = {};

    private static final int[] NO_INTS = {};

    private static final Type[] NO_TYPES = {};

    private static final JMethod[] NO_CALLEES = {};

    private final ClassHierarchy hierarchy;

    private final Iterable<R> source;

    private final int capacity;

    private final Function<? super R, Type> typeOf;

    private boolean copied;

    private Object[] receivers = NO_RECEIVERS;

    /**
     * Dense id of each receiver's type, indexed like {@link #receivers}.
     */
    private int[] typeIds = NO_INTS;

    /**
     * The distinct receiver types, indexed by type id.
     */
    private Type[] types = NO_TYPES;

    /**
     * Answer of the hierarchy for each type id under the current target;
     * valid only where {@link #stamps} equals {@link #generation}.
     */
    private JMethod[] callees = NO_CALLEES;

    private int[] stamps = NO_INTS;

    private int size;

    /**
     * Number of the current target, starting at 1, so that the zeroed
     * {@link #stamps} mark no answer as known.
     */
    private int generation;

    private @Nullable JMethod target;

    private @Nullable MethodRef ref;

    /**
     * @param source   the receivers; iterated once, at the first target
     * @param capacity the number of receivers in {@code source}
     * @param typeOf   the type of a receiver
     */
    ReceiverDispatch(ClassHierarchy hierarchy, Iterable<R> source,
                     int capacity, Function<? super R, Type> typeOf) {
        this.hierarchy = hierarchy;
        this.source = source;
        this.capacity = capacity;
        this.typeOf = typeOf;
    }

    /**
     * Starts dispatching {@code target}; copies the receivers at the first
     * call.
     */
    void startTarget(JMethod target) {
        if (!copied) {
            copy();
            copied = true;
        }
        this.target = target;
        ref = null;
        ++generation;
    }

    private void copy() {
        Object[] objs = new Object[capacity];
        int[] ids = new int[capacity];
        Type[] distinct = new Type[capacity];
        Map<Type, Integer> idOf = new HashMap<>();
        source.forEach(receiver -> {
            Type type = typeOf.apply(receiver);
            Integer id = idOf.get(type);
            if (id == null) {
                id = idOf.size();
                idOf.put(type, id);
                distinct[id] = type;
            }
            objs[size] = receiver;
            ids[size] = id;
            ++size;
        });
        receivers = objs;
        typeIds = ids;
        types = distinct;
        callees = new JMethod[idOf.size()];
        stamps = new int[idOf.size()];
    }

    /**
     * @return the number of receivers; valid after {@link #startTarget}.
     */
    int size() {
        return size;
    }

    /**
     * @return the {@code i}-th receiver in iteration order.
     */
    @SuppressWarnings("unchecked")
    R receiver(int i) {
        return (R) receivers[i];
    }

    /**
     * @return the method that the {@code i}-th receiver runs for the current
     * target, or {@code null} if the target cannot be dispatched on that
     * receiver's type.
     */
    @Nullable JMethod dispatch(int i) {
        int id = typeIds[i];
        if (stamps[id] != generation) {
            if (ref == null) {
                ref = target.getRef();
            }
            callees[id] = hierarchy.dispatch(types[id], ref);
            stamps[id] = generation;
        }
        return callees[id];
    }
}
