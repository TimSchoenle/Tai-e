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

import pascal.taie.World;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Stream;

/**
 * Static utility methods for modeling the behaviors of reflection APIs.
 */
public final class Reflections {

    private Reflections() {
    }

    public static Stream<JMethod> getDeclaredConstructors(JClass jclass) {
        return jclass.getDeclaredMethods()
                .stream()
                .filter(JMethod::isConstructor);
    }

    public static Stream<JMethod> getConstructors(JClass jclass) {
        return getDeclaredConstructors(jclass).filter(ClassMember::isPublic);
    }

    public static Stream<JMethod> getDeclaredMethods(JClass jclass, String methodName) {
        return jclass.getDeclaredMethods()
                .stream()
                .filter(m -> m.getName().equals(methodName));
    }

    public static Stream<JMethod> getDeclaredMethods(JClass jclass) {
        return jclass.getDeclaredMethods()
                .stream()
                .filter(m -> !m.isConstructor() && !m.isStaticInitializer());
    }

    /*
     * getMethods(JClass, String) answers from a per-class memo instead of walking the superclass chain on every
     * call. The memo of a class maps each method name to the list the original walk returns for it: one walk over
     * all public declared methods of the class and its superclasses, keeping the first method per subsignature,
     * grouped by name in walk order. Subsignatures of different names never collide, so per name this is exactly the
     * original's walk. A class's declared methods and superclass are fixed once the world is built
     * (JClass.declaredMethods is unmodifiable), so the memo never goes stale within a world; it is cleared when the
     * world is reset. -Dspd.reflections.verify=true compares every answer with the original walk and fails on any
     * difference.
     */
    private static final Map<JClass, Map<String, List<JMethod>>> PUBLIC_METHODS_BY_NAME =
            new ConcurrentHashMap<>();

    private static final boolean VERIFY = Boolean.getBoolean("spd.reflections.verify");

    private static final AtomicLong VERIFIED = new AtomicLong();

    static {
        World.registerResetCallback(PUBLIC_METHODS_BY_NAME::clear);
        if (VERIFY) {
            Runtime.getRuntime().addShutdownHook(new Thread(() ->
                    System.err.println("[spd] Reflections.getMethods verified calls: " + VERIFIED.get())));
        }
    }

    public static Stream<JMethod> getMethods(JClass jclass, String methodName) {
        List<JMethod> methods = PUBLIC_METHODS_BY_NAME
                .computeIfAbsent(jclass, Reflections::publicMethodsByName)
                .getOrDefault(methodName, List.of());
        if (VERIFY) {
            List<JMethod> expected = walkMethods(jclass, methodName);
            if (!expected.equals(methods)) {
                throw new AssertionError("Reflections.getMethods differs for " + jclass + "." + methodName
                        + ": expected " + expected + ", got " + methods);
            }
            long n = VERIFIED.incrementAndGet();
            if (Long.bitCount(n) == 1) {
                System.err.println("[spd] Reflections.getMethods verified calls: " + n);
            }
        }
        return methods.stream();
    }

    private static Map<String, List<JMethod>> publicMethodsByName(JClass start) {
        Map<String, List<JMethod>> byName = new HashMap<>();
        Set<Subsignature> subSignatures = new HashSet<>();
        for (JClass c = start; c != null; c = c.getSuperClass()) {
            for (JMethod m : c.getDeclaredMethods()) {
                if (m.isPublic() && subSignatures.add(m.getSubsignature())) {
                    byName.computeIfAbsent(m.getName(), n -> new ArrayList<>()).add(m);
                }
            }
        }
        byName.replaceAll((n, list) -> List.copyOf(list));
        return byName;
    }

    /** The original walk, kept for the verify mode. */
    private static List<JMethod> walkMethods(JClass jclass, String methodName) {
        List<JMethod> methods = new ArrayList<>();
        Set<Subsignature> subSignatures = Sets.newHybridSet();
        while (jclass != null) {
            jclass.getDeclaredMethods()
                    .stream()
                    .filter(m -> m.isPublic() && m.getName().equals(methodName))
                    .filter(m -> !subSignatures.contains(m.getSubsignature()))
                    .forEach(m -> {
                        methods.add(m);
                        subSignatures.add(m.getSubsignature());
                    });
            jclass = jclass.getSuperClass();
        }
        return methods;
    }

    public static Stream<JMethod> getMethods(JClass jclass) {
        List<JMethod> methods = new ArrayList<>();
        Set<Subsignature> subSignatures = Sets.newHybridSet();
        while (jclass != null) {
            jclass.getDeclaredMethods()
                    .stream()
                    .filter(JMethod::isPublic)
                    .filter(m -> !m.isConstructor() && !m.isStaticInitializer())
                    .filter(m -> !subSignatures.contains(m.getSubsignature()))
                    .forEach(m -> {
                        methods.add(m);
                        subSignatures.add(m.getSubsignature());
                    });
            jclass = jclass.getSuperClass();
        }
        return methods.stream();
    }
}
