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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.util.CSObjs;
import pascal.taie.analysis.pta.plugin.util.InvokeHandler;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Reflections;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Sets;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;
import java.util.stream.Stream;

import static pascal.taie.analysis.pta.plugin.util.InvokeUtils.BASE;

public class StringBasedModel extends InferenceModel {

    /**
     * Option {@code reflection-members}: model the field lookups and the
     * member arrays below (px/s115-rmp). Off keeps upstream's results.
     */
    private final boolean members;

    StringBasedModel(Solver solver, MetaObjHelper helper, Set<Invoke> invokesWithLog) {
        super(solver, helper, invokesWithLog);
        members = solver.getOptions().getBoolean("reflection-members");
    }

    /**
     * Class.getField and Class.getDeclaredField of a known class and a
     * string constant name: the meta objects of the fields of that name, so
     * that Field.get and Field.set move objects (px/s115-rmp; upstream
     * creates field meta objects only from a reflection log). getField
     * resolves a public field of the class or of any supertype; every such
     * field of the name is taken, a superset of the one the JVM picks.
     */
    @InvokeHandler(signature = {
            "<java.lang.Class: java.lang.reflect.Field getField(java.lang.String)>",
            "<java.lang.Class: java.lang.reflect.Field getDeclaredField(java.lang.String)>"},
            argIndexes = {BASE, 0})
    public void classGetField(Context context, Invoke invoke,
                              PointsToSet classObjs, PointsToSet nameObjs) {
        Var result = invoke.getResult();
        if (!members || result == null || invokesWithLog.contains(invoke)) {
            return;
        }
        boolean declared = isDeclaredLookup(invoke, "getDeclaredField", "getField");
        classObjs.forEach(classObj -> {
            JClass clazz = CSObjs.toClass(classObj);
            if (clazz == null) {
                return;
            }
            nameObjs.forEach(nameObj -> {
                String name = CSObjs.toString(nameObj);
                if (name != null) {
                    fields(clazz, declared)
                            .filter(field -> field.getName().equals(name))
                            .map(helper::getMetaObj)
                            .forEach(fieldObj -> solver.addVarPointsTo(context, result, fieldObj));
                }
            });
        });
    }

    /**
     * Class.get[Declared][Methods|Constructors|Fields]() of a known class:
     * an array (one per call site and context) whose elements are the meta
     * objects of every member the call returns (px/s115-rmp; upstream
     * string-constant inference left these arrays without elements).
     */
    @InvokeHandler(signature = {
            "<java.lang.Class: java.lang.reflect.Method[] getMethods()>",
            "<java.lang.Class: java.lang.reflect.Method[] getDeclaredMethods()>",
            "<java.lang.Class: java.lang.reflect.Constructor[] getConstructors()>",
            "<java.lang.Class: java.lang.reflect.Constructor[] getDeclaredConstructors()>",
            "<java.lang.Class: java.lang.reflect.Field[] getFields()>",
            "<java.lang.Class: java.lang.reflect.Field[] getDeclaredFields()>"},
            argIndexes = {BASE})
    public void classGetMembers(Context context, Invoke invoke, PointsToSet classObjs) {
        Var result = invoke.getResult();
        if (!members || result == null || invokesWithLog.contains(invoke)) {
            return;
        }
        CSObj array = csManager.getCSObj(context, helper.getMetaObjArray(invoke));
        ArrayIndex elements = csManager.getArrayIndex(array);
        String api = invoke.getMethodRef().getName();
        classObjs.forEach(classObj -> {
            JClass clazz = CSObjs.toClass(classObj);
            if (clazz != null) {
                members(clazz, api)
                        .map(helper::getMetaObj)
                        .forEach(member -> solver.addPointsTo(elements, member));
                solver.addVarPointsTo(context, result, array);
            }
        });
    }

    private static Stream<? extends ClassMember> members(JClass clazz, String api) {
        return switch (api) {
            case "getMethods" -> Reflections.getMethods(clazz);
            case "getDeclaredMethods" -> Reflections.getDeclaredMethods(clazz);
            case "getConstructors" -> Reflections.getConstructors(clazz);
            case "getDeclaredConstructors" -> Reflections.getDeclaredConstructors(clazz);
            case "getFields" -> fields(clazz, false);
            case "getDeclaredFields" -> fields(clazz, true);
            default -> throw new AnalysisException("Unexpected member API " + api);
        };
    }

    /**
     * The fields of {@code clazz}: its declared fields, or its public
     * fields and the public fields of every supertype.
     */
    private static Stream<JField> fields(JClass clazz, boolean declared) {
        if (declared) {
            return clazz.getDeclaredFields().stream();
        }
        return supertypes(clazz).stream()
                .flatMap(type -> type.getDeclaredFields().stream())
                .filter(JField::isPublic);
    }

    /** {@code clazz} and all its superclasses and superinterfaces, transitively. */
    private static Set<JClass> supertypes(JClass clazz) {
        Set<JClass> types = Sets.newLinkedSet();
        Deque<JClass> work = new ArrayDeque<>();
        work.add(clazz);
        while (!work.isEmpty()) {
            JClass type = work.poll();
            if (types.add(type)) {
                if (type.getSuperClass() != null) {
                    work.add(type.getSuperClass());
                }
                work.addAll(type.getInterfaces());
            }
        }
        return types;
    }

    private static boolean isDeclaredLookup(Invoke invoke, String declared, String inherited) {
        String name = invoke.getMethodRef().getName();
        if (name.equals(declared)) {
            return true;
        }
        if (name.equals(inherited)) {
            return false;
        }
        throw new AnalysisException("Expected [" + declared + ", " + inherited + "], given " + invoke.getMethodRef());
    }

    @InvokeHandler(signature = {
            "<java.lang.Class: java.lang.Class forName(java.lang.String)>",
            "<java.lang.Class: java.lang.Class forName(java.lang.String,boolean,java.lang.ClassLoader)>",
            "<java.lang.ClassLoader: java.lang.Class loadClass(java.lang.String)>"},
            argIndexes = {0})
    public void classForName(Context context, Invoke invoke, PointsToSet nameObjs) {
        if (invokesWithLog.contains(invoke)) {
            return;
        }
        nameObjs.forEach(obj ->
                classForNameKnown(context, invoke, CSObjs.toString(obj)));
    }

    @InvokeHandler(signature = {
            "<java.lang.Class: java.lang.reflect.Constructor getConstructor(java.lang.Class[])>",
            "<java.lang.Class: java.lang.reflect.Constructor getDeclaredConstructor(java.lang.Class[])>"},
            argIndexes = {BASE})
    public void classGetConstructor(Context context, Invoke invoke, PointsToSet classObjs) {
        if (invokesWithLog.contains(invoke)) {
            return;
        }
        classObjs.forEach(obj ->
                classGetConstructorKnown(context, invoke, CSObjs.toClass(obj)));
    }

    @InvokeHandler(signature = {
            "<java.lang.Class: java.lang.reflect.Method getMethod(java.lang.String,java.lang.Class[])>",
            "<java.lang.Class: java.lang.reflect.Method getDeclaredMethod(java.lang.String,java.lang.Class[])>"},
            argIndexes = {BASE, 0})
    public void classGetMethod(Context context, Invoke invoke,
                               PointsToSet classObjs, PointsToSet nameObjs) {
        if (invokesWithLog.contains(invoke)) {
            return;
        }
        classObjs.forEach(classObj -> {
            JClass clazz = CSObjs.toClass(classObj);
            nameObjs.forEach(nameObj -> {
                String name = CSObjs.toString(nameObj);
                classGetMethodKnown(context, invoke, clazz, name);
            });
        });
    }

    @InvokeHandler(signature = {
            "<java.lang.reflect.Method: java.lang.Class getDeclaringClass()>"
    }, argIndexes = {BASE})
    public void methodGetDeclaringClass(Context context, Invoke invoke, PointsToSet methodObjs) {
        if (invokesWithLog.contains(invoke)) {
            return;
        }
        methodObjs.forEach(methodObj -> {
            JMethod jMethod = CSObjs.toMethod(methodObj);
            if (jMethod != null) {
                classForNameKnown(context, invoke, jMethod.getDeclaringClass().getName());
            }
        });
    }
}
