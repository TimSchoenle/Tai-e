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
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.type.ClassType;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.List;
import java.util.Set;

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
 * ({@link MemberFieldUnification}): a superset of the eager field contents,
 * so no flow is lost.
 * <p>
 * With {@code -Dpx.lazymembers.verify=true}, {@link #verify} checks every
 * placeholder and its consumers at the end of the analysis
 * ({@link LazyMembersVerifier}).
 */
public final class LazyMembers {

    /**
     * Descriptor of the placeholder objects. Its equality and hash code come
     * from its text, as the hash code of the placeholder's allocation
     * ({@link MemberSummary}) does, so neither of these two parts of the
     * placeholder's hash code is an identity hash. (Its type's hash code, the
     * third part, is the {@code ClassType}'s, as for every object of that
     * type.)
     */
    static final Descriptor LAZY_DESC = new TextDescriptor("LazyReflectionMetaObj");

    private final int threshold;

    private final HeapModel heapModel;

    private final TwoKeyMap<Invoke, Context, MemberSummary> summaries = Maps.newTwoKeyMap();

    private final @Nullable LazyMembersVerifier verifier;

    /**
     * @param threshold      the number of receiver classes a call site takes
     *                       eagerly in one call context, at least 0
     * @param invokesWithLog the calls resolved by the reflection log, whose
     *                       consumers take no inferred member object
     */
    LazyMembers(Solver solver, int threshold, Set<Invoke> invokesWithLog) {
        if (threshold < 0) {
            throw new IllegalArgumentException("lazy member threshold " + threshold);
        }
        this.threshold = threshold;
        this.heapModel = solver.getHeapModel();
        this.verifier = LazyMembersVerifier.isEnabled()
                ? new LazyMembersVerifier(solver, invokesWithLog)
                : null;
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
                    s -> heapModel.getMockObj(LAZY_DESC, s, type), verifier);
            summaries.put(invoke, context, summary);
        }
        return summary;
    }

    /**
     * Runs the in-run check when it is enabled.
     *
     * @throws IllegalStateException if a placeholder or a consumer missed a
     *                               member
     */
    void verify() {
        if (verifier != null) {
            verifier.verify(summaries.values());
        }
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

    /**
     * The member-retrieving call site of placeholder {@code obj}. Its
     * container, its index there and its API ({@link Invoke#getMethodRef})
     * name the placeholder deterministically, together with {@link #context}.
     *
     * @throws IllegalArgumentException if {@code obj} is not a placeholder
     */
    public static Invoke site(Obj obj) {
        return summaryOf(obj).invoke();
    }

    /**
     * The call context of the call site of placeholder {@code obj}: there is
     * one placeholder per (call site, call context).
     *
     * @throws IllegalArgumentException if {@code obj} is not a placeholder
     */
    public static Context context(Obj obj) {
        return summaryOf(obj).context();
    }

    private static MemberSummary summaryOf(Obj obj) {
        if (obj.getAllocation() instanceof MemberSummary summary) {
            return summary;
        }
        throw new IllegalArgumentException("not a lazy member placeholder: " + obj);
    }

    /**
     * A descriptor equal to every descriptor of this class with the same
     * text, whose hash code is the text's.
     */
    private record TextDescriptor(String string) implements Descriptor {

        @Override
        public int hashCode() {
            return string.hashCode();
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof TextDescriptor other && string.equals(other.string);
        }
    }
}
