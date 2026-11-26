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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.List;

/**
 * Lazy reflection members (option {@code reflection-members-lazy: N},
 * px/s115-P52). A member-retrieving call site (the member arrays,
 * getField/getDeclaredField, getMethod/getDeclaredMethod,
 * getConstructor/getDeclaredConstructor) takes its first N distinct
 * receiver classes in each call context eagerly, as concrete member objects,
 * and every later class lazily: its members go into one placeholder object
 * per (call site, call context) instead, whose allocation is a
 * {@link MemberSummary}. The placeholder has the type of the concrete member
 * objects ({@code Method}, {@code Constructor} or {@code Field}) and the
 * empty heap context, as they do. Consumers resolve concrete and
 * placeholder objects alike through {@link MemberObjs#forEachMember}.
 * <p>
 * Member objects carry instance fields that code stores into and loads
 * from. A placeholder and a concrete member object (or two placeholders)
 * holding the same member are different heap objects, so with lazy members
 * all member objects of one kind share their instance fields
 * ({@link #unifiedBase}): a superset of the eager field contents, so no
 * flow is lost.
 */
public final class LazyMembers {

    /**
     * Descriptor of the placeholder objects.
     */
    static final Descriptor LAZY_DESC = () -> "LazyReflectionMetaObj";

    /**
     * Descriptor of the objects whose instance fields stand for those of all
     * member objects of one kind.
     */
    private static final Descriptor MEMBER_FIELDS_DESC = () -> "ReflectionMemberFields";

    private final int threshold;

    private final HeapModel heapModel;

    private final CSManager csManager;

    private final Context emptyContext;

    private final MetaObjHelper helper;

    private final TwoKeyMap<Invoke, Context, MemberSummary> summaries = Maps.newTwoKeyMap();

    private @Nullable CSObj methodFields;

    private @Nullable CSObj constructorFields;

    private @Nullable CSObj fieldFields;

    /**
     * @param threshold the number of receiver classes a call site takes
     *                  eagerly in one call context, at least 0
     */
    LazyMembers(Solver solver, MetaObjHelper helper, int threshold) {
        if (threshold < 0) {
            throw new IllegalArgumentException("lazy member threshold " + threshold);
        }
        this.threshold = threshold;
        this.heapModel = solver.getHeapModel();
        this.csManager = solver.getCSManager();
        this.emptyContext = solver.getContextSelector().getEmptyContext();
        this.helper = helper;
    }

    /**
     * @return the summary of {@code invoke} in {@code context}, made on first
     * use with its placeholder object of type {@code type}
     */
    MemberSummary summary(Invoke invoke, Context context, ClassType type,
                          MemberSummary.Source source, boolean named) {
        MemberSummary summary = summaries.get(invoke, context);
        if (summary == null) {
            summary = new MemberSummary(invoke, context, source, named, threshold,
                    s -> heapModel.getMockObj(LAZY_DESC, s, type));
            summaries.put(invoke, context, summary);
        }
        return summary;
    }

    /**
     * The base whose instance fields stand for those of {@code base}: for a
     * member object (concrete or placeholder) one object per member kind,
     * for any other object {@code base} itself.
     */
    CSObj unifiedBase(CSObj base) {
        Obj obj = base.getObject();
        if (!(obj instanceof MockObj mock)
                || !(mock.getDescriptor().equals(LAZY_DESC) || helper.isInferredMemberObj(obj))) {
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

    /**
     * @return whether {@code obj} is a lazy member placeholder
     */
    public static boolean isPlaceholder(Obj obj) {
        return obj.getAllocation() instanceof MemberSummary;
    }

    /**
     * @return the members of placeholder {@code obj} so far, in delivery
     * order (a view that grows with the placeholder)
     * @throws IllegalArgumentException if {@code obj} is not a placeholder
     */
    public static List<ClassMember> members(Obj obj) {
        return summaryOf(obj).members();
    }

    private static MemberSummary summaryOf(Obj obj) {
        if (obj.getAllocation() instanceof MemberSummary summary) {
            return summary;
        }
        throw new IllegalArgumentException("not a lazy member placeholder: " + obj);
    }
}
