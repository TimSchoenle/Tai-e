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

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.language.classes.ClassMember;

import java.util.function.Consumer;

/**
 * The one way a consumer reads the member that a member object stands for
 * (px/s115-P52). A concrete member object (inferred or from the reflection
 * log) stands for one member; a lazy member placeholder
 * ({@link LazyMembers}) for the members of its summary, which grow.
 */
public final class MemberObjs {

    private MemberObjs() {
    }

    /**
     * Hands every member that {@code obj} stands for to {@code action}: for
     * a concrete member object its member, now; for a placeholder its
     * members so far, now, and every later member when it is added. Any
     * other object stands for no member. A consumer calls this once per
     * (consumer call site, object), as it takes each object once.
     */
    public static void forEachMember(CSObj obj, Consumer<? super ClassMember> action) {
        Object alloc = obj.getObject().getAllocation();
        if (alloc instanceof ClassMember member) {
            action.accept(member);
        } else if (alloc instanceof MemberSummary summary) {
            summary.subscribe(action);
        }
    }
}
