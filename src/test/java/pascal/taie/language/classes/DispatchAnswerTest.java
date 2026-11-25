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

package pascal.taie.language.classes;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.frontend.java.classes.PhantomClassBuilder;
import pascal.taie.frontend.java.classes.PhantomClassSource;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.IntType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.language.type.VoidType;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link ClassHierarchyImpl#dispatch(JClass, MethodRef)} keeps its final answer per receiver class and method
 * reference, and {@link ClassHierarchyImpl#dispatch(Type, MethodRef)} looks {@code java.lang.Object} up once for
 * array receivers; every answer equals the uncached one: the subclass check, then the lookup.
 */
class DispatchAnswerTest {

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world",
                "--input-classes", "Hierarchy,DefaultMethod,PhantomField");
    }

    private static JClassLoader worldBootstrapLoader() {
        return World.get().getClassHierarchy().getBootstrapClassLoader();
    }

    private static JClass worldClass(String name) {
        JClass c = World.get().getClassHierarchy().getClass(name);
        assertNotNull(c, name);
        return c;
    }

    private static @Nullable JMethod uncached(
            ClassHierarchyImpl hierarchy, JClass receiver, MethodRef ref) {
        return hierarchy.isSubclass(ref.getDeclaringClass(), receiver)
                ? hierarchy.lookupDispatchTarget(receiver, ref.getSubsignature())
                : null;
    }

    /**
     * Every receiver class of the world against the methods of its supertypes (hits, abstract and default
     * methods, interfaces, phantom classes), the methods of an unrelated class (failed subclass checks) and an
     * absent method; then array receivers against the methods of {@code java.lang.Object}.
     */
    @Test
    void everyAnswerEqualsTheUncachedDispatch() {
        ClassHierarchyImpl hierarchy = (ClassHierarchyImpl) World.get().getClassHierarchy();
        TypeSystem typeSystem = World.get().getTypeSystem();
        List<JClass> classes = hierarchy.allClasses().toList();
        List<String> mismatches = new ArrayList<>();
        int pairs = 0;
        int hits = 0;
        int lookupMisses = 0;
        int subclassMisses = 0;
        int interfaceRefs = 0;
        int defaultTargets = 0;
        int phantomReceivers = 0;
        for (int i = 0; i < classes.size(); i++) {
            JClass receiver = classes.get(i);
            Set<MethodRef> refs = new LinkedHashSet<>();
            for (JClass s : supertypes(receiver)) {
                s.getDeclaredMethods().forEach(m -> refs.add(m.getRef()));
            }
            classes.get((i + 1) % classes.size()).getDeclaredMethods().forEach(m -> refs.add(m.getRef()));
            refs.add(MethodRef.get(receiver, "noSuchMethod", List.of(), VoidType.VOID, false));
            if (receiver.isPhantom()) {
                phantomReceivers++;
                refs.add(MethodRef.get(receiver, "phantomMethod", List.of(), IntType.INT, false));
            }
            for (MethodRef ref : refs) {
                pairs++;
                boolean related = hierarchy.isSubclass(ref.getDeclaringClass(), receiver);
                JMethod expected = uncached(hierarchy, receiver, ref);
                JMethod first = hierarchy.dispatch(receiver, ref);
                JMethod second = hierarchy.dispatch(receiver, ref);
                if (expected != first || first != second) {
                    mismatches.add(receiver + " " + ref + " expected=" + expected
                            + " first=" + first + " second=" + second);
                }
                if (!related) {
                    subclassMisses++;
                } else if (expected == null) {
                    lookupMisses++;
                } else {
                    hits++;
                    if (expected.getDeclaringClass().isInterface() && !expected.isAbstract()) {
                        defaultTargets++;
                    }
                }
                if (ref.getDeclaringClass().isInterface()) {
                    interfaceRefs++;
                }
            }
        }
        JClass object = hierarchy.getJREClass(ClassNames.OBJECT);
        assertNotNull(object);
        List<MethodRef> objectRefs = new ArrayList<>();
        object.getDeclaredMethods().forEach(m -> objectRefs.add(m.getRef()));
        objectRefs.add(MethodRef.get(object, "noSuchMethod", List.of(), VoidType.VOID, false));
        objectRefs.add(worldClass("C").getDeclaredMethods().iterator().next().getRef());
        int arrayPairs = 0;
        for (ArrayType array : List.of(typeSystem.getArrayType(IntType.INT, 1),
                typeSystem.getArrayType(typeSystem.objectType(), 2))) {
            for (MethodRef ref : objectRefs) {
                arrayPairs++;
                JMethod expected = uncached(hierarchy, object, ref);
                JMethod first = hierarchy.dispatch(array, ref);
                JMethod second = hierarchy.dispatch(array, ref);
                if (expected != first || first != second) {
                    mismatches.add(array + " " + ref + " expected=" + expected
                            + " first=" + first + " second=" + second);
                }
            }
        }
        String counts = "pairs " + pairs + " (hits " + hits + ", lookup misses " + lookupMisses
                + ", subclass misses " + subclassMisses + ", interface refs " + interfaceRefs
                + ", default targets " + defaultTargets + ", phantom receivers " + phantomReceivers
                + "), array pairs " + arrayPairs + ", classes " + classes.size();
        assertEquals(List.of(), mismatches, counts);
        assertTrue(hits > 0 && lookupMisses > 0 && subclassMisses > 0 && interfaceRefs > 0
                && defaultTargets > 0 && phantomReceivers > 0 && arrayPairs > 0, counts);
    }

    private static Set<JClass> supertypes(JClass c) {
        Set<JClass> seen = new HashSet<>();
        Deque<JClass> work = new ArrayDeque<>();
        work.add(c);
        while (!work.isEmpty()) {
            JClass x = work.poll();
            if (seen.add(x)) {
                JClass superClass = x.getSuperClass();
                if (superClass != null) {
                    work.add(superClass);
                }
                work.addAll(x.getInterfaces());
            }
        }
        return seen;
    }

    /**
     * Counts the subclass checks of {@link ClassHierarchyImpl#dispatch(JClass, MethodRef)}.
     */
    private static final class CountingSubclassChecks extends ClassHierarchyImpl {

        private int checks;

        @Override
        public boolean isSubclass(JClass superclass, JClass subclass) {
            ++checks;
            return super.isSubclass(superclass, subclass);
        }
    }

    @Test
    void subclassCheckRunsOncePerReceiverAndReference() {
        JClass c = worldClass("C");
        MethodRef bar = MethodRef.get(c, "bar", List.of(), VoidType.VOID, false);
        MethodRef absent = MethodRef.get(c, "noSuchMethod", List.of(), VoidType.VOID, false);
        CountingSubclassChecks hierarchy = new CountingSubclassChecks();
        JMethod target = hierarchy.dispatch(c, bar);
        assertNotNull(target);
        assertSame(target, hierarchy.dispatch(c, bar));
        assertSame(target, hierarchy.dispatch(c, bar));
        assertNull(hierarchy.dispatch(c, absent));
        assertNull(hierarchy.dispatch(c, absent));
        assertEquals(2, hierarchy.checks);
    }

    /**
     * Counts the lookups of {@code java.lang.Object} by name.
     */
    private static final class CountingObjectLookups extends ClassHierarchyImpl {

        private int lookups;

        @Override
        public JClass getJREClass(String name) {
            if (ClassNames.OBJECT.equals(name)) {
                ++lookups;
            }
            return super.getJREClass(name);
        }
    }

    @Test
    void arrayReceiverLooksObjectUpOncePerBootstrapLoader() {
        CountingObjectLookups hierarchy = new CountingObjectLookups();
        hierarchy.setBootstrapClassLoader(worldBootstrapLoader());
        JClass object = hierarchy.getJREClass(ClassNames.OBJECT);
        assertNotNull(object);
        hierarchy.lookups = 0;
        MethodRef hashCode = MethodRef.get(object, "hashCode", List.of(), IntType.INT, false);
        ArrayType ints = World.get().getTypeSystem().getArrayType(IntType.INT, 1);
        JMethod target = hierarchy.dispatch(ints, hashCode);
        assertNotNull(target);
        assertSame(object, target.getDeclaringClass());
        assertSame(target, hierarchy.dispatch(ints, hashCode));
        assertEquals(1, hierarchy.lookups);
        hierarchy.setBootstrapClassLoader(worldBootstrapLoader());
        assertSame(target, hierarchy.dispatch(ints, hashCode));
        assertEquals(2, hierarchy.lookups);
    }

    /**
     * A loader that finds no class, so the subclass check has no {@code java.lang.Object} to compare with.
     */
    private static final class EmptyLoader implements JClassLoader {

        @Override
        public @Nullable JClass loadClass(String name) {
            return null;
        }

        @Override
        public @Nullable JClass loadClass(String name, boolean allowPhantom) {
            return null;
        }

        @Override
        public Collection<JClass> getLoadedClasses() {
            return List.of();
        }
    }

    @Test
    void loaderChangeClearsTheAnswers() {
        JClass iface = worldClass("I");
        JClass object = World.get().getClassHierarchy().getJREClass(ClassNames.OBJECT);
        assertNotNull(object);
        MethodRef hashCode = MethodRef.get(object, "hashCode", List.of(), IntType.INT, false);
        for (boolean bootstrap : new boolean[]{true, false}) {
            ClassHierarchyImpl hierarchy = new ClassHierarchyImpl();
            if (bootstrap) {
                hierarchy.setBootstrapClassLoader(new EmptyLoader());
            } else {
                hierarchy.setDefaultClassLoader(new EmptyLoader());
            }
            JMethod before = hierarchy.dispatch(iface, hashCode);
            assertSame(uncached(hierarchy, iface, hashCode), before);
            if (bootstrap) {
                hierarchy.setBootstrapClassLoader(worldBootstrapLoader());
            } else {
                hierarchy.setDefaultClassLoader(worldBootstrapLoader());
            }
            JMethod after = uncached(hierarchy, iface, hashCode);
            assertTrue(before != after, "the loader changes the answer");
            assertSame(after, hierarchy.dispatch(iface, hashCode));
        }
    }

    /**
     * Answers the subclass check from a switch, standing for a check whose answer a new class changes.
     */
    private static final class SwitchedSubclassCheck extends ClassHierarchyImpl {

        private boolean related;

        @Override
        public boolean isSubclass(JClass superclass, JClass subclass) {
            return related;
        }
    }

    @Test
    void addedClassClearsTheAnswers() {
        JClass c = worldClass("C");
        JClass d = worldClass("D");
        MethodRef bar = MethodRef.get(c, "bar", List.of(), VoidType.VOID, false);
        SwitchedSubclassCheck hierarchy = new SwitchedSubclassCheck();
        assertNull(hierarchy.dispatch(d, bar));
        hierarchy.related = true;
        assertNull(hierarchy.dispatch(d, bar), "the answer is kept until a class is added");
        String name = "DispatchAnswerTest$Added";
        JClass added = new JClass(worldBootstrapLoader(), name, (String) null);
        new PhantomClassBuilder(World.get().getTypeSystem(), new PhantomClassSource(name, true)).build(added);
        hierarchy.addClass(added);
        JMethod target = hierarchy.dispatch(d, bar);
        assertNotNull(target);
        assertSame(c, target.getDeclaringClass());
    }
}
