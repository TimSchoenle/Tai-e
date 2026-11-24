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

/**
 * Dispatches one reflectively invoked instance method on the receiver
 * objects of one {@code Method.invoke} handler call. The method reference
 * is built at the first dispatch, once, not once per receiver, and the
 * hierarchy is asked once per receiver type. For one type and one reference
 * the answer cannot change: loading classes adds classes but never changes
 * a loaded class's supertypes or methods.
 * <p>
 * The answer for the latest new type is kept in fields; a map is created
 * only when a second receiver type arrives.
 */
final class ReceiverDispatch {

    /**
     * Stands for a {@code null} answer in {@link #earlier}, so that one
     * lookup tells a known type without a callee from an unknown type.
     */
    private static final Object NO_CALLEE = new Object();

    private final ClassHierarchy hierarchy;

    private final JMethod target;

    private @Nullable MethodRef ref;

    private @Nullable Type lastType;

    private @Nullable JMethod lastCallee;

    /**
     * Answers of the hierarchy for the types before {@link #lastType}: the
     * callee, or {@link #NO_CALLEE} for a {@code null} answer; created at the
     * second type.
     */
    private @Nullable Map<Type, Object> earlier;

    ReceiverDispatch(ClassHierarchy hierarchy, JMethod target) {
        this.hierarchy = hierarchy;
        this.target = target;
    }

    /**
     * @return the method that a receiver of {@code receiverType} runs, or
     * {@code null} if the method cannot be dispatched on that type.
     */
    @Nullable JMethod dispatch(Type receiverType) {
        if (receiverType.equals(lastType)) {
            return lastCallee;
        }
        if (earlier != null) {
            Object answer = earlier.get(receiverType);
            if (answer != null) {
                return answer == NO_CALLEE ? null : (JMethod) answer;
            }
        }
        if (lastType != null) {
            if (earlier == null) {
                earlier = new HashMap<>();
            }
            earlier.put(lastType, lastCallee != null ? lastCallee : NO_CALLEE);
        }
        if (ref == null) {
            ref = target.getRef();
        }
        lastType = receiverType;
        lastCallee = hierarchy.dispatch(receiverType, ref);
        return lastCallee;
    }
}
