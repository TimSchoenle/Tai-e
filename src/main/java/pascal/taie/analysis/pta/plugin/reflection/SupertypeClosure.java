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
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The classes that may declare an instance member accessible on an object
 * of a given type, computed once per type.
 * <p>
 * For a class type: the class, its superclasses and its superinterfaces,
 * transitively, and {@code java.lang.Object}. For an array type:
 * {@code java.lang.Object} only, as {@code ClassHierarchy.dispatch}
 * dispatches on an array as on {@code Object}, and the other supertypes of
 * an array ({@code Cloneable}, {@code Serializable}) declare no instance
 * members. Any other type, and a class type without a class, has none.
 * <p>
 * This is the relation that {@code ClassHierarchy.isSubclass(declaring,
 * receiver)} answers, which {@code ClassHierarchy.dispatch} checks before it
 * looks a method up, and that {@code TypeSystem.isSubtype} answers for an
 * instance field's declaring class. Loading classes adds classes but never
 * changes the supertypes of a loaded class, so an answer stays valid.
 */
final class SupertypeClosure {

    private final @Nullable JClass objectClass;

    private final Map<Type, List<JClass>> closures = Maps.newMap();

    SupertypeClosure(ClassHierarchy hierarchy) {
        this.objectClass = hierarchy.getJREClass(ClassNames.OBJECT);
    }

    /**
     * @return the classes that may declare an instance member accessible on
     * an object of {@code type}; the same list for the same type.
     */
    List<JClass> of(Type type) {
        List<JClass> closure = closures.get(type);
        if (closure == null) {
            closure = compute(type);
            closures.put(type, closure);
        }
        return closure;
    }

    private List<JClass> compute(Type type) {
        if (type instanceof ClassType classType) {
            JClass jclass = classType.getJClass();
            return jclass == null ? List.of() : closure(jclass);
        }
        if (type instanceof ArrayType) {
            return objectClass == null ? List.of() : List.of(objectClass);
        }
        return List.of();
    }

    private List<JClass> closure(JClass jclass) {
        Set<JClass> types = Sets.newLinkedSet();
        Deque<JClass> work = new ArrayDeque<>();
        work.add(jclass);
        while (!work.isEmpty()) {
            JClass type = work.poll();
            if (types.add(type)) {
                JClass superClass = type.getSuperClass();
                if (superClass != null) {
                    work.add(superClass);
                }
                for (JClass iface : type.getInterfaces()) {
                    // a class loader without phantom classes gives null
                    // for an interface missing from the class path
                    if (iface != null) {
                        work.add(iface);
                    }
                }
            }
        }
        if (objectClass != null) {
            types.add(objectClass);
        }
        return List.copyOf(types);
    }
}
