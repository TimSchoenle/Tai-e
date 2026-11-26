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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;

/**
 * Member-field unification (px/s115-P52): all member objects of one kind
 * ({@code Method}, {@code Constructor} or {@code Field}), concrete objects of
 * reflection inference and lazy member placeholders alike, share their
 * instance fields. A placeholder and a concrete member object (or two
 * placeholders) holding the same member are different heap objects, so
 * without it a value stored through one and loaded through the other would
 * be lost; with it, the field contents are a superset of the eager ones.
 * <p>
 * It is on whenever lazy members are, and on its own with option
 * {@code reflection-members-unify} to measure what it adds to an eager run.
 * It covers every member object of a kind, not only the kinds that end up
 * with a lazy call site: it must be installed before the first instance
 * field exists, and whether a call site turns lazy is known only later, so a
 * unification switched on later would miss the values already stored into
 * the separate fields of the concrete objects.
 */
final class MemberFieldUnification {

    /**
     * Descriptor of the objects whose instance fields stand for those of all
     * member objects of one kind.
     */
    private static final Descriptor MEMBER_FIELDS_DESC = () -> "ReflectionMemberFields";

    private final HeapModel heapModel;

    private final CSManager csManager;

    private final Context emptyContext;

    private final MetaObjHelper helper;

    private @Nullable CSObj methodFields;

    private @Nullable CSObj constructorFields;

    private @Nullable CSObj fieldFields;

    private MemberFieldUnification(Solver solver, MetaObjHelper helper) {
        this.heapModel = solver.getHeapModel();
        this.csManager = solver.getCSManager();
        this.emptyContext = solver.getContextSelector().getEmptyContext();
        this.helper = helper;
    }

    /**
     * Makes the member objects of {@code solver} share their instance
     * fields, before the solver creates any instance field.
     */
    static void install(Solver solver, MetaObjHelper helper) {
        MemberFieldUnification unification = new MemberFieldUnification(solver, helper);
        solver.getCSManager().unifyInstanceFieldBases(unification::unifiedBase);
    }

    /**
     * The base whose instance fields stand for those of {@code base}: for a
     * member object (concrete or placeholder) one object per member kind,
     * for any other object {@code base} itself.
     */
    private CSObj unifiedBase(CSObj base) {
        Obj obj = base.getObject();
        if (!(obj instanceof MockObj mock)
                || !(mock.getDescriptor().equals(LazyMembers.LAZY_DESC)
                || helper.isInferredMemberObj(obj))) {
            return base;
        }
        Type type = obj.getType();
        if (type.equals(helper.method)) {
            if (methodFields == null) {
                methodFields = memberFields(helper.method);
            }
            return methodFields;
        } else if (type.equals(helper.constructor)) {
            if (constructorFields == null) {
                constructorFields = memberFields(helper.constructor);
            }
            return constructorFields;
        } else if (type.equals(helper.field)) {
            if (fieldFields == null) {
                fieldFields = memberFields(helper.field);
            }
            return fieldFields;
        }
        throw new IllegalStateException("member object of type " + type + ": " + obj);
    }

    private CSObj memberFields(ClassType type) {
        return csManager.getCSObj(emptyContext,
                heapModel.getMockObj(MEMBER_FIELDS_DESC, type, type));
    }
}
